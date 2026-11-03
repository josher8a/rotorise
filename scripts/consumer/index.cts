import {
    array,
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
