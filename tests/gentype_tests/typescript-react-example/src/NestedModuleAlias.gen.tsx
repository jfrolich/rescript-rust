/* TypeScript file generated from NestedModuleAlias.res by genType. */

/* eslint-disable */
/* tslint:disable */

import * as NestedModuleAliasJS from './NestedModuleAlias.res.js';

import type {Transcript_data as NestedTypes_Transcript_data} from './NestedTypes.gen';

export type Transcript_word = { readonly index: number; readonly text: string };

export type Transcript_data = { readonly words: Transcript_word[] };

export const words: (data:NestedTypes_Transcript_data) => number = NestedModuleAliasJS.words as any;
