import { native } from 'rotorise/native'

// A project that imports `rotorise/native` and no other entry. The declaration of each constant
// names the type of `native`, and the emitter reaches that type through this entry only.
export const Marshal = native({ removeUndefinedValues: true })
export const Bare = native
