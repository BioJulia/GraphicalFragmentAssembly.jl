module GraphicalFragmentAssembly

using StringViews: StringView
using TranscodingStreams: TranscodingStream, NoopStream
using Automa: Automa, RegExp as RE
using Automa.RegExp: @re_str
using Automa.Stream: @mark, @markpos
using BioGenerics: BioGenerics

# TODO: Make better context - goto, maybe simd maybe with unroll?
const AUTOMA_CONTEXT = Automa.CodeGenContext(;
    vars=Automa.Variables(:p, :p_end, :p_eof, :ts, :te, :cs, :data, :mem, :byte)
)

struct Unsafe end
const unsafe = Unsafe()

"""
    LazyRecord

A semi-parsed GFA record. Only the record type and the location of the optional data
is parsed. Use `rectype` to get the record type, `materialize` to create a real record object,
and `optionals` to get a lazy iterator of `LazyOptional` fields.
"""
mutable struct LazyRecord
    # The entire line is copied in here raw with tabs, but without the
    # final newline
    buffer::Vector{UInt8}
    # First integer in optional is the final non-optional byte + 2
    # E.g. in line "H\tAB:i:5", optional is 3:8.
    # For missing optional e.g. "H", it's 3:2, to mark that the
    # optional data would have begun at index 3, but is empty.
    # Hence the non-optional data is always 1:first(optional)-2
    optional::UnitRange{Int}
    # First byte of each line, e.g. UInt8('S') for a segment line
    type::UInt8
end

# Empty lazy records are headers by default
LazyRecord() = LazyRecord(UInt8[], 3:2, UInt8('H'))

function empty!(x::LazyRecord)
    x.optional = 3:2
    x.type = UInt8('H')
end

Base.copy(x::LazyRecord) = LazyRecord(copy(x.buffer), x.optional, x.type)
rectype(x::LazyRecord) = unsafe_char(x.type)

# Unsafe in that the byte must be ASCII for this to be valid
unsafe_char(x::UInt8) = reinterpret(Char, (x % UInt32) << 24)

function append_from!(dst, dpos, src, spos, n)
    if length(dst) < dpos + n - 1
        resize!(dst, dpos + n - 1)
    end
    # TODO: Could add unsafe_copyto! here, once the package
    # is properly tested
    copyto!(dst, dpos, src, spos, n)
    return dst
end

function materialize(record::LazyRecord)
    # TODO: All records must have its own materilize function
    if record.type == UInt8('H')
        return materialize_header(record)
    else
        error("Invalid record type")
    end
end

include("optional.jl")
using .Optional

GFA_MACHINE = let
    tabs(arg, args...) = foldl((i, j) -> i * re"\t" * j, args; init=arg)
    newline = let
        lf = re"\n"
        lf.actions[:enter] = [:count_line]
        RE.opt(re"\r") * lf
    end
    comment = re"#[^\n]*"

    # This byte marks the entry into optional fields, which we have a separate
    # machine to handle to avoid single machines being insanely complex
    optional_entry = re"\t"
    optional_entry.actions[:enter] = [:enter_optional]
    name = re"[!-)+-<>-~][!-~]*"
    plusminus = re"\+|-"
    cigar = re"\*" | re"([0-9]+[MIDNSHPX=])+"
    int = re"[0-9]+"

    header = re"H"
    segment = tabs(re"S", name, (re"\*" | re"[A-Za-z=.]+"))
    link = tabs(re"L", name, plusminus, name, plusminus, cigar)
    # Specs's int regex in containment claims it can be empty - this might be a typo.
    # We require at least one digit here.
    containment = tabs(re"C", name, plusminus, name, plusminus, int, cigar)
    path_overlaps = re"\*" | RE.rep1(cigar | re"[-+]?[0-9]+J" | re"\.")
    path = tabs(re"P", name, name, path_overlaps)
    optint = re"\*" | int
    walk = tabs(re"W", name, int, name, optint, optint, re"([><][!-;=?-~]+)+")
    jump = tabs(re"J", name, plusminus, name, plusminus, re"\*|([-+]?[0-9]+)")


    line = (header | segment | link | containment | path | walk | jump) * RE.opt(optional_entry)
    line.actions[:enter] = [:enter_line]
    line.actions[:exit] = [:exit_line]
    line_or_comment = line | comment

    gfa = line_or_comment * RE.rep(newline * line_or_comment) * RE.rep(newline)
    Automa.compile(gfa)
end

const GFA_ACTIONS = Dict(
    :count_line => :(linenum += 1),
    :enter_line => quote
        @mark
        record.type = byte
    end,
    # At the end of a line, we append the entire line to the lazy record,
    # including all tabs and so on, but not including final \r?\n
    :exit_line => quote
        data_length = p - @markpos
        append_from!(record.buffer, 1, data, @markpos, data_length)
        # Set bufferpos back one byte so next record begins at the same byte
        # where the machine left off.
        # We guarantee the bufferpos is not 0, because the buffer has its
        # mark set at the beginning of the record
        buffer.bufferpos -= 1
        # The optional field is set if optional data is encountered.
        # If not, we still need to set the field in order to signal
        # where the non-optional data ends
        if isempty(record.optional)
            record.optional = data_length + 2 : data_length - 1
        end
        found = true
        # This pseudo-macro is manually detected in Automa's compiler,
        # it's not a real Julia macro. It breaks the machine's main loop.
        # The reason it's just a break statement is because the existence of
        # a while loop to even break is an implementation detail,
        # and indeed it does not exist in e.g. the goto-generator.
        @escape
    end,
    # This section is complicated by the fact that the index_optional! function reads
    # the buffered stream, and so may shift data around inside the stream's buffer
    :enter_optional => quote
        # We're at the tab now, so optional data starts at p+1
        optional_start = p + 1
        record_optional_index = p - @markpos() + 2
        # Read the optional data and mark its position in the record,
        # and also update p.
        # p is the final p of the optional machine, because a final e.g. '\n' byte
        # must be read twice: Once in the optional machine, to end it, and once here,
        # to trigger the proper state transition.
        p = index_optional!(stream, record, tags, optional_start, linenum, record_optional_index) - 1
        # We need to update the bufferpos here, because the Automa-generated function
        # read_record! will set p to be equal to buffer.bufferpos if the buffer reaches p_end,
        # and data has to move inside the buffer.
        # Hence, we do this to not lose the value of p we just set above.
        buffer.bufferpos = p
        # It is possible that the optional machine has resized the buffer underlying
        # data. If that's the case, then the mem variable points to now-invalid data.
        # So redefine it.
        mem = Automa.SizedMemory(data)
    end
)

function read_record! end

Automa.Stream.generate_reader(
    :read_record!,
    GFA_MACHINE;
    arguments = (:(record::LazyRecord), :(tags::Vector{Tag}), :(linenum::Int), :(state::Int)),
    actions = GFA_ACTIONS,
    context = AUTOMA_CONTEXT,
    initcode = quote
        linenum = 1
        # Init byte here so it's visible in the entire function scope
        byte = 0x00
        found = false
        cs = state
    end,
    loopcode = quote
        # @goto __return__ will make the machine exit the loop generated by
        # the autogenerated read_record! function.
        # TODO: Better error message, potentially using Automa's fancy new errors?
        found && @goto __return__
    end,
    returncode = :(return cs, linenum, found)
) |> eval

# TODO: Parameterize the reader by :lazy or :eager to allow eagerly materializing
# the LazyRecord for when performance does not matter.
# Also perhaps make it handle GFA versions 1 and 2?
mutable struct Reader{S <: TranscodingStream} <: BioGenerics.IO.AbstractReader
    const stream::S
    const record::LazyRecord
    # We store all tags of the optional fields in this buffer,
    # in order to check for duplicate tags.
    # We assume no more than 64 tags per line.
    const tag_buffer::Vector{Tag}
    # To be able to continue after reading a single record, the Automa state
    # must be able to be reset to where the reader left off
    automa_state::Int
    linenum::Int
    # Whether to automatically copy out the record or read in-place
    const copy::Bool

    function Reader{T}(io::T, copy::Bool) where {T <: TranscodingStream}
        v = Vector{UInt8}(undef, 2048)
        @inbounds v[1] = UInt8('H')
        record = LazyRecord(v, 3:2, UInt8('H'))
        new{T}(io, record, Vector{Tag}(undef, 64), 1, 1, copy)
    end
end

Base.eltype(::Type{<:Reader}) = LazyRecord
Reader(io::TranscodingStream; copy::Bool=true) = Reader{typeof(io)}(io, copy)
Reader(io::IO; kwargs...) = Reader(NoopStream(io); kwargs...)

function tryread!(reader::Reader, record::LazyRecord)
    (state, linenum, found) = read_record!(reader.stream, record, reader.tag_buffer, reader.linenum, reader.automa_state)
    if !found
        # If the state is zero, but the record was not found, then the machine
        # did not error, but also, there was no record. So, IO must be EOF.
        iszero(state) && return nothing
        throw(ArgumentError(lazy"Malformed GFA file on line $linenum"))
    end
    reader.linenum = linenum
    reader.automa_state = state
    return record
end

function Base.read!(reader::Reader, record::LazyRecord)
    y = tryread!(reader, record)
    y === nothing ? throw(EOFError()) : record
end

function Base.iterate(reader::Reader, _::Nothing=nothing)::Union{Nothing, Tuple{LazyRecord, Nothing}}
    y = tryread!(reader, reader.record)
    return if y === nothing
        nothing
    else
        record = reader.copy ? copy(reader.record) : reader.record
        (record, nothing)
    end
end

struct Header
    version::Union{String, Nothing}
end

function materialize_header(record::LazyRecord)
    version = get(optionals(record), Tag("VN"), nothing)::Union{String, Nothing}
    Header(version)
end

#=
using GraphicalFragmentAssembly

data = "#abcdef\r\nH\tVS:i:-199\nH\nH\tAB:A:z"
reader = GraphicalFragmentAssembly.Reader(IOBuffer(data))
collect(reader)

GraphicalFragmentAssembly.read_record!(io, rec, 1, 1)
GraphicalFragmentAssembly.read_record!(io, rec, 1, 4)
=#

#=
using GraphicalFragmentAssembly
using TranscodingStreams
v = UInt8[]
data = "VN:Z:somedata\tXA:i:-1991\tKX:f:-19.33E-21\tAA:A:z\nSOMEMOREDATA"

io = NoopStream(IOBuffer(data))
GraphicalFragmentAssembly.append_optional!(io, v, 1)
=#


end # module