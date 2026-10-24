/* TypeScript file generated from ModuleAliasImport.res by genType. */

/* eslint-disable */
/* tslint:disable */

import * as ModuleAliasImportJS from './ModuleAliasImport.res.js';

import type {num as $$Imported_num} from './MyMath';

import type {num as ImportedTypes_num} from './ImportedTypes.gen';

import type {numberOrString as $$Imported_numberOrString} from './MyMath';

import type {numberOrString as ImportedTypes_numberOrString} from './ImportedTypes.gen';

export type Imported_num = $$Imported_num;

export type Imported_numberOrString = $$Imported_numberOrString;

export const keep: (x:ImportedTypes_num) => ImportedTypes_num = ModuleAliasImportJS.keep as any;

export const keepEither: (x:ImportedTypes_numberOrString) => ImportedTypes_numberOrString = ModuleAliasImportJS.keepEither as any;
