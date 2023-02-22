module Optional

# TODO: Add validation of only 1 of same Optional in same line

using GraphicalFragmentAssembly: Unsafe, unsafe, LazyRecord, AUTOMA_CONTEXT, append_from!, unsafe_char
import GraphicalFragmentAssembly: materialize
using Automa: Automa, RegExp as RE
using Automa.RegExp: @re_str
using Automa.Stream: @mark, @markpos
using StringViews: StringView

export Tag, OptionalFields, optionals, LazyOptional, JSONString, index_optional!

const B_ARRAY_TYPES_DICT = Dict(
    'c' => Int8,
    'C' => UInt8,
    's' => Int16,
    'S' => UInt16,
    'i' => Int32,
    'I' => UInt32,
    'f' => Float32
)

const BArrayTypes = Union{values(B_ARRAY_TYPES_DICT)...}

const OptTypes = Union{Char, Int, Float32, String, Vector{<:BArrayTypes}}

# Technically, adding more parameters to Base Julian types is not breaking, but if some genious
# decides to do it in the future, this type turns into a UnionAll type, which will wreck
# the performance of all containers that store views, so please don't do this.
const ViewType = SubArray{UInt8, 1, Vector{UInt8}, Tuple{UnitRange{Int64}}, true}
@assert typeof(view([0x61], 1:1)) == ViewType

struct Tag <: AbstractString
    x::NTuple{2, UInt8}

    Tag(x::NTuple{2, UInt8}, ::Unsafe) = new(x)
end

function Tag(x::NTuple{2, UInt8})
    a, b = x
    if !(a in UInt8('A'):UInt8('Z') || a in UInt8('z'):UInt8('z')) ||
       !(b in UInt8('A'):UInt8('Z') || b in UInt8('z'):UInt8('z') || b in UInt8('0'):UInt8('9'))
       error("Tag must match regex [A-Za-z][A-Za-z0-9]")
    end
    Tag(x, unsafe)
end

function Tag(s::Union{String, SubString{String}})
    ncodeunits(s) == 2 || error("String must have 2 codeunits")
    Tag((@inbounds codeunit(s, 1), @inbounds codeunit(s, 2)))
end
Base.convert(::Type{Tag}, x::Union{String, SubString{String}}) = Tag(x)
function Base.convert(::Type{Tag}, x::NTuple{2, T}) where {T <: Union{UInt8, Char}}
    Tag((UInt8(x[1]), UInt8(x[2])))
end

Base.String(x::Tag) = string(unsafe_char(x.x[1]), unsafe_char(x.x[2]))
Base.convert(::Type{String}, x::Tag) = String(x)

Base.codeunits(x::Tag) = x.x
Base.ncodeunits(::Tag) = 2
Base.isvalid(::Tag, i::Integer) = i == 1 || i == 2
Base.length(::Tag) = 2
Base.iterate(s::Tag, i::Int=1) = i > 2 ? nothing : (unsafe_char(s.x[i]), i+1)

struct LazyOptional
    type::UInt8
    data::ViewType
end

function Base.show(io::IO, x::LazyOptional)
    print(io, "LazyOptional(", repr(Char(x.type)), ", ", x.data, ')')
end

LazyOptional(type::Char, data::Vector{UInt8}) = LazyOptional(UInt8(type), view(data, 1:length(data)))

struct OptionalFields <: AbstractDict{Tag, LazyOptional}
    x::LazyRecord
end
optionals(x::LazyRecord) = OptionalFields(x)

function materialize(x::OptionalFields)
    result = Dict{Tag, OptTypes}()
    for (k, v) in x
        haskey(result, k) && error(lazy"Duplicate optional tag \"$k\"")
        result[k] = materialize(v)
    end
    result
end

function Base.length(x::OptionalFields)
    if isempty(x.x.optional)
        0
    else
        count(isequal(UInt8('\t')), view(x.x.buffer, x.x.optional)) + 1
    end
end

Base.IteratorSize(::Type{OptionalFields}) = Base.SizeUnknown()

function Base.iterate(x::OptionalFields, state=first(x.x.optional))
    state > last(x.x.optional) && return nothing
    buffer = x.x.buffer
    start_pos = state + 5
    final_pos = let
        p = findnext(isequal(UInt8('\t')), buffer, state+6)
        p === nothing ? last(x.x.optional) : (p - 1)
    end
    data = view(buffer, start_pos:final_pos)
    tag = Tag((buffer[state], buffer[state+1]), unsafe)
    lazytag = LazyOptional(buffer[state+3], data)
    (tag => lazytag, final_pos + 2)
end

function Base.get(x::OptionalFields, k, default)
    key = convert(Tag, k)
    for (tag, value) in x
        tag == key && return value
    end
    return default
end

function Base.getindex(x::OptionalFields, k)
    key = convert(Tag, k)
    y = get(x, key, nothing)
    y === nothing && throw(KeyError(key))
    y
end

struct JSONString
    x::String
end

function materialize(tag::LazyOptional)::OptTypes
    type = tag.type
    data = tag.data
    if type == UInt8('A')
        unsafe_char(data[1])
    elseif type == UInt8('i')
        parse(Int, StringView(data); base=10)
    elseif type == UInt8('f')
        parse(Float32, StringView(data))
    elseif type == UInt8('Z')
        String(data)
    elseif type == UInt8('J')
        JSONString(String(data))
    elseif type == UInt8('H')
        hex2bytes(data)
    elseif type == UInt8('B')
        T = B_ARRAY_TYPES_DICT[unsafe_char(data[1])]
        s = StringView(view(data, 2:lastindex(data)))
        [parse(T, i) for i in eachsplit(s, ',')]::Vector{<:BArrayTypes}
    end
end

function check_duplicates(v::Vector{Tag}, n::Int, linenum::Int)
    length(v) ≥ n || throw(BoundsError(v, n))
    @inbounds for i in 1:n-1
        a = v[1]
        for j in i+1:n
            b = v[j]
            a == b && error(lazy"Duplicate tag on line $linenum: \"$a\"")
        end
    end
    nothing
end

const OPTIONAL_MACHINE = let
    signed = re"[-+]?[0-9]+"
    unsigned = re"\+?[0-9]+"
    float = re"[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?"
    string = re"[ !-~]+"

    sint_B = re"[csi]" * RE.rep1(re"," * signed)
    uint_B = re"[CSI]" * RE.rep1(re"," * unsigned)
    float_B = re"f" * RE.rep1(re"," * float)
    val_B = sint_B | uint_B | float_B
    tag = re"[A-Za-z][A-Za-z0-9]"
    tag.actions[:exit] = [:new_tag]

    field = tag * re":" * RE.alt(
        re"A:[!-~]",
        re"i:" * signed,
        re"f:" * float,
        re"[ZJ]:" * string,
        re"H:[0-9A-F]+",
        re"B:" * val_B
    )
    
    line = field * RE.rep(re"\t" * field)
    line.actions[:exit] = [:exit_machine]
    Automa.compile(line * RE.opt(re"[\r\n]"))
end

const OPTIONAL_ACTIONS = Dict(
    :new_tag => quote
        n_tags += 1
        tag = Tag((data[p-2], data[p-1]), unsafe)
        tags[n_tags] = tag
    end,
    :exit_machine => quote
        optional_length = p - from + p_decremented
        record.optional = record_index:record_index+optional_length-1
        check_duplicates(tags, n_tags, linenum)
        return p
    end
)

Automa.Stream.generate_reader(
    :index_optional!,
    OPTIONAL_MACHINE;
    arguments = (:(record::LazyRecord), :(tags::Vector{Tag}), :(from::Int), :(linenum::Int), :(record_index::Int)),
    context = AUTOMA_CONTEXT,
    actions = OPTIONAL_ACTIONS,
    initcode = quote
        byte = 0x00
        n_tags = 0
        p_decremented = 0
        buffer.bufferpos = from
    end,
    # The Base.skip in the generated code can decrement bufferpos, after which
    # p is decremented by the same amount.
    # Keep track of how much this is, so we know how many bytes the optional data is
    loopcode = quote
        cs < 0 && error(lazy"Error when parsing optional fields on line $linenum")
        p_decremented += p - buffer.bufferpos
    end
) |> eval

end