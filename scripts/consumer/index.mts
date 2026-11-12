import {
    array,
    type Attribute,
    type AttributeMap,
    boolean,
    type Decoded,
    discriminatedUnion,
    type Encoded,
    exclude,
    extract,
    item,
    list,
    number,
    object,
    optional,
    ref,
    type Result,
    scope,
    string,
    tableEntry,
    union,
} from 'rotorise'
import { arbitraryOf, checkRoundTrip, rngFrom } from 'rotorise/testing'
import { native } from 'rotorise/native'

type Pet =
    | { petId: string; kind: 'DOG'; ownerId: string }
    | { petId: string; kind: 'CAT' }

export const Pets = tableEntry<Pet>()({
    PK: ['petId'],
    SK: {
        discriminator: 'kind',
        spec: { DOG: ['ownerId'], CAT: null },
    },
})

export const Dog = object({ kind: string('DOG'), name: string, age: optional(number) })
export const Cat = object({ kind: string('CAT'), name: string, lives: number })
export const Animal = union([Dog, Cat])
export const Tagged = discriminatedUnion('kind', [Dog, Cat])
export const Dogs = extract(Animal, object({ kind: string('DOG') }))
export const NotDogs = exclude(Animal, object({ kind: string('DOG') }))
export const { Tree } = scope({
    Tree: object({ name: string, children: optional(array(ref('Tree'))) }),
})
export const Litters = object({ litter: list(string, number), vaccinated: boolean })

export type AnimalValue = Decoded<typeof Animal>
export type AnimalStored = Encoded<typeof Animal>
export const dog: Decoded<typeof Dogs> = { kind: 'DOG', name: 'Rex' }
export const stored = Dogs.unsafeEncode(dog)
export const cat: Decoded<typeof NotDogs> = { kind: 'CAT', name: 'Tom', lives: 9 }
export const sample: Decoded<typeof Tree> = { name: 'pets', children: [{ name: 'dogs' }] }
export const marshalled = native({ removeUndefinedValues: true })
export const roundTrip = checkRoundTrip(item(Dog))
export const generated = arbitraryOf(Animal, rngFrom(1), 3)

// A call that the types refuse, inside a thunk that a function takes: the shape of `expect(() => ...)`.
// The refusal must reach the end of the walk of the key on every compiler.
declare const expectThrow: <T>(actual: T) => { toThrow: () => void }
export const refused = expectThrow(() =>
    tableEntry<Pet>()(
        { PK: ['petId'] },
        // @ts-expect-error an empty separator joins no segments apart
        { separator: '' },
    ),
).toThrow()

// A pin holds in both directions. An annotation accepts a result of `never`, because `never` is
// assignable to each type, and a result of `any`, by the rule of the language. So the call states the
// pin as a type argument, and the rest parameter refuses the call where the result and the pin are not
// the same type. An `any` inside an object stays out of reach, so each computed member has its own pin.
type Unequal<Pinned, Result> = 0 extends 1 & Result
    ? ['the result is `any`']
    : [Result] extends [Pinned]
      ? [Pinned] extends [Result]
          ? []
          : ['the result is narrower than the pin']
      : ['the result is wider than the pin']
declare const pinned: <Pinned>() => <Result>(
    result: Result,
    ...unequal: Unequal<Pinned, Result>
) => Result

// The methods of an entry with a codec. Each result type is pinned, so a compiler that resolves a type
// in another way refuses the constant.
type Kennel = { petId: string; shelterId: string; name: string; age: number }
export const Kennels = tableEntry<Kennel>()(
    { PK: ['petId'], SK: ['name'], GSI1PK: 'shelterId', GSI1SK: ['age'] },
    {
        codec: { petId: string, shelterId: string, name: string, age: number },
        key: { partition: 'PK', sort: 'SK' },
        indexes: { GSI1: { partition: 'GSI1PK', sort: 'GSI1SK' } },
    },
)
const kennel: Kennel = { petId: 'p1', shelterId: 's1', name: 'Rex', age: 3 }
const ids = { petId: 'p1' } as const
const shelter = { shelterId: 's1' } as const
const older = { age: 4 } as const
export const kennelKey = pinned<'PETID#p1'>()(Kennels.key('PK', ids))
export const kennelKeyOfOne = pinned<'s1'>()(Kennels.key('GSI1PK', shelter))
export const kennelKeyOfEntity = pinned<`NAME#${string}`>()(Kennels.key('SK', kennel))
export const kennelEntry = pinned<
    Kennel & {
        readonly PK: `PETID#${string}`
        readonly SK: `NAME#${string}`
        readonly GSI1PK: string
        readonly GSI1SK: `AGE#${number}`
    }
>()(Kennels.toEntry(kennel))
export const kennelEntryPK = pinned<`PETID#${string}`>()(Kennels.toEntry(kennel).PK)
export const kennelEntrySK = pinned<`NAME#${string}`>()(Kennels.toEntry(kennel).SK)
export const kennelEntryGSI1PK = pinned<string>()(Kennels.toEntry(kennel).GSI1PK)
export const kennelEntryGSI1SK = pinned<`AGE#${number}`>()(Kennels.toEntry(kennel).GSI1SK)
export const kennelKeys = pinned<AttributeMap>()(Kennels.keys(['PK', 'SK'], kennel))
export const kennelConditionName = pinned<'PK'>()(Kennels.keyCondition(ids).partition.name)
export const kennelUpdateRemove = pinned<readonly 'GSI1PK'[]>()(Kennels.keyUpdates(older).remove)
export const kennelItem = pinned<
    Result<{
        readonly petId: Attribute<'S'>
        readonly shelterId: Attribute<'S'>
        readonly name: Attribute<'S'>
        readonly age: Attribute<'N'>
        readonly PK: Attribute<'S'>
        readonly SK: Attribute<'S'>
        readonly GSI1PK: Attribute<'S'>
        readonly GSI1SK: Attribute<'S'>
    }>
>()(Kennels.toItem(kennel))
export const kennelFrom = pinned<Result<Kennel>>()(
    Kennels.fromItem({
        petId: { S: 'p1' },
        shelterId: { S: 's1' },
        name: { S: 'Rex' },
        age: { N: '3' },
    }),
)
export const kennelPath = pinned<string>()(Kennels.path().name.toString())
const pet: Pet = { petId: 'p1', kind: 'CAT' }
export const petKey = pinned<'PETID#p1'>()(Pets.key('PK', ids))
export const petKeyOfEntity = pinned<`PETID#${string}`>()(Pets.key('PK', pet))
