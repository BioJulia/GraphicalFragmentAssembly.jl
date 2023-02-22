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
    # The optional data is copied in here raw with tabs
    buffer::Vector{UInt8}
    # First integer in optional is the final non-optional byte + 2
    # E.g. in line "H\tAB:i:5", optional is 3:8.
    # For missing optional, it's 1:0
    optional::UnitRange{Int}
    type::UInt8
end

# Empty lazy records are comments by default
LazyRecord() = LazyRecord(UInt8[], 1:0, UInt8('#'))

function empty!(x::LazyRecord)
    x.optional = 1:0
    x.type = UInt8('#')
end

Base.copy(x::LazyRecord) = LazyRecord(copy(x.buffer), x.optional, x.type)

rectype(x::LazyRecord) = unsafe_char(x.type)

# Unsafe in that the byte must be ASCII for this to be valid
unsafe_char(x::UInt8) = reinterpret(Char, (x % UInt32) << 24)

function append_from!(dst, dpos, src, spos, n)
    if length(dst) < dpos + n - 1
        resize!(dst, dpos + n - 1)
    end
    # TODO: Could add unsafe_copyto! here
    copyto!(dst, dpos, src, spos, n)
    return dst
end

function materialize(record::LazyRecord)
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
        # where the machine left off
        buffer.bufferpos -= 1
        # The optional field is set if optional data is encountered.
        # If not, we still need to set the field in order to signal
        # where the non-optional data ends
        if isempty(record.optional)
            record.optional = data_length + 1 : data_length
        end
        found = true
        @escape
    end,
    :enter_optional => quote
        # We're at the tab now, so optional data starts at p+1
        optional_start = p + 1
        record_optional_index = p - @markpos() + 2
        # Read the optional data and mark its position in the record,
        # and also update p.
        p = index_optional!(stream, record, optional_start, linenum, record_optional_index) - 1
        buffer.bufferpos = p
        # It is possible that the optional machine has resized the buffer underlying
        # data. If that's the case, then the mem variable points to now-invalid data.
        # So redefine it
        mem = Automa.SizedMemory(data)
    end
)

Automa.Stream.generate_reader(
    :read_record!,
    GFA_MACHINE;
    arguments = (:(record::LazyRecord), :(linenum::Int), :(state::Int)),
    actions = GFA_ACTIONS,
    context = AUTOMA_CONTEXT,
    initcode = quote
        linenum = 1
        byte = 0x00
        found = false
        empty!(record)
        cs = state
    end,
    loopcode = quote
        # TODO: Better error message, potentially using Automa's fancy new errors?
        found && @goto __return__
    end,
    returncode = :(return cs, linenum, found)
) |> eval

mutable struct Reader{S <: TranscodingStream} <: BioGenerics.IO.AbstractReader
    const stream::S
    const record::LazyRecord
    automa_state::Int
    linenum::Int
    # Current record, to be copied out if necessary
    # Whether to automatically copy out the record
    const copy::Bool

    function Reader{T}(io::T, copy::Bool) where {T <: TranscodingStream}
        v = Vector{UInt8}(undef, 2048)
        @inbounds v[1] = UInt8('#')
        record = LazyRecord(v, 1:0, UInt8('#'))
        new{T}(io, record, 1, 1, copy)
    end
end

Base.eltype(::Type{<:Reader}) = LazyRecord
Reader(io::TranscodingStream; copy::Bool=true) = Reader{typeof(io)}(io, copy)
Reader(io::IO; kwargs...) = Reader(NoopStream(io); kwargs...)

function tryread!(reader::Reader, record::LazyRecord)
    (state, linenum, found) = read_record!(reader.stream, record, reader.linenum, reader.automa_state)
    if !found
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
    tag = convert(Tag, "VN")
    version = nothing
    for (k, v) in optionals(record)
        k == tag && (version = materialize(v)::String)
    end
    Header(version)
end

#=
using GraphicalFragmentAssembly
using TranscodingStreams

data = "#abcdef\r\nH\tVS:i:-199\nH\nH\tAB:A:z"
rec = GraphicalFragmentAssembly.LazyRecord()
io = NoopStream(IOBuffer(data); bufsize=3)

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