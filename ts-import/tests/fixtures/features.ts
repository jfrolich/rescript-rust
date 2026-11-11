// One export per TypeScript feature. `tests/catalog.rs` imports the whole
// module and compares the ReScript declarations with `features.res.txt`.

// --- primitives and literals ---
export declare const aString: string;
export declare const aNumber: number;
export declare const aBoolean: boolean;
export declare const aBigint: bigint;
export declare const aSymbol: symbol;
export declare const nothing: undefined;
export declare const aNull: null;
export const literalString = "hello";
export const literalNumber = 42;
export declare const stringLiteralType: "on";
export declare function returnsVoid(): void;

// --- null and undefined ---
export declare const maybeString: string | undefined;
export declare const nullableString: string | null;
export declare const nullishString: string | null | undefined;
export declare function find(id: string): { id: string } | undefined;

// --- arrays and tuples ---
export declare const numbers: number[];
export declare const readonlyNumbers: readonly number[];
export declare const pair: [string, number];
export declare const triple: readonly [string, number, boolean];
export declare const single: [string];
export declare const optionalTuple: [string, number?];
export declare const restTuple: [string, ...number[]];
export const constTuple = ["a", 1] as const;

// --- objects ---
export interface Point { x: number; y: number }
export interface Options { readonly name: string; retries?: number; "content-type"?: string; type: string }
export interface Nested { point: Point; inline: { a: number; b: { c: string } } }
export declare const dictionary: { [key: string]: number };
export declare const record: Record<string, Point>;
export declare const keyedRecord: Record<"a" | "b", number>;
export declare const mixedIndex: { known: string; [key: string]: string };
export declare const emptyObject: {};
export declare const anyObject: object;
export const inferredObject = { host: "localhost", port: 8080, tags: ["a"] };

// --- functions ---
export declare function twoArgs(a: string, b: number): boolean;
export declare function optionalArg(a: string, b?: number): string;
export function defaultArg(a: string, b = 10) { return a.length + b; }
export declare function restArgs(first: string, ...rest: number[]): void;
export declare function callback(done: (error: Error | null, value?: string) => void): void;
export declare function restCallback(f: (...args: number[]) => number): void;
export declare function returnsFunction(prefix: string): (name: string) => string;
export declare function overloaded(value: string): string;
export declare function overloaded(value: number): number;
export declare function withThis(this: Point, scale: number): Point;
export declare function isString(value: unknown): value is string;
export declare function assertString(value: unknown): asserts value is string;
export const arrow = async (id: number) => ({ id, label: String(id) });

// --- generics ---
export declare function identity<T>(value: T): T;
export declare function mapArray<T, U>(items: T[], f: (item: T, index: number) => U): U[];
export declare function constrained<T extends { id: string }>(item: T): T;
export declare function pluck<T, K extends keyof T>(item: T, key: K): T[K];
export interface Box<T> { value: T; map<U>(f: (value: T) => U): Box<U> }
export type Pair<A, B> = { first: A; second: B };
export declare function genericCallback(run: <T>(value: T) => T): void;
export type Maybe<T> = T | undefined;
export declare function maybe<T>(value: T): Maybe<T>;

// --- unions ---
export type Direction = "up" | "down" | "left" | "right";
export type Digit = 0 | 1 | 2;
export type Size = "auto" | number;
export type StringOrNumber = string | number;
export type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; size: number }
  | { kind: "empty" };
export type Outcome<T> = { ok: true; value: T } | { ok: false; error: string };
export type ById = { type: 1; id: number } | { type: 2; name: string };
export type OneOrMany = string | string[];
export type Loose = { a: string } | { b: number };
export type Json = string | number | boolean | null | Json[] | { [key: string]: Json };
export type Callback = (() => void) | string;
export type DateOrText = Date | string;
export type Falsy = false | "" | 0 | null | undefined;

// --- enums ---
export enum Color { Red, Green, Blue }
export enum Level { Low = "low", High = "high" }
export const enum Flag { A = 1, B = 2 }
export declare function paint(color: Color, level: Level, flag: Flag): void;
export declare function onlyRed(color: Color.Red): void;

// --- classes ---
export class Animal {
  static count = 0;
  static create(name: string): Animal { return new Animal(name); }
  #hidden = 1;
  private secret = 2;
  protected family = "x";
  constructor(public readonly name: string, public legs = 4) {}
  speak(loud?: boolean): string { return this.name; }
  get shout(): string { return this.name.toUpperCase(); }
  rename(name: string): this { return this; }
}
export class Dog extends Animal { fetch(thing: string): Promise<string> { return Promise.resolve(thing); } }
export class Stack<T> { private items: T[] = []; push(item: T): void {} pop(): T | undefined { return undefined; } get size(): number { return 0; } }
export abstract class Base { abstract id(): string }
export declare function adopt(animal: Animal): Dog;
export declare const AnimalClass: typeof Animal;

// --- interfaces ---
export interface Named { name: string }
export interface Employee extends Named { salary: number; manager?: Employee }
export interface Callable { (input: string): number }
export interface Hybrid { (input: string): number; version: string }
export interface Constructable { new (name: string): Named }
export interface Tree { value: number; children: Tree[] }

// --- type operators, resolved by the checker ---
export type PartialOptions = Partial<Options>;
export type PickedPoint = Pick<Nested, "point">;
export type WithoutType = Omit<Options, "type">;
export type RequiredOptions = Required<Options>;
export type PointKeys = keyof Point;
export type PointX = Point["x"];
export type Returned = ReturnType<typeof twoArgs>;
export type Params = Parameters<typeof twoArgs>;
export type Unwrapped = Awaited<Promise<Point>>;
export type NonNull = NonNullable<string | null | undefined>;
export type Getters = { [K in keyof Point as `get${Capitalize<K>}`]: () => Point[K] };
export type Conditional<T> = T extends string ? "text" : "other";
export declare const resolvedConditional: Conditional<string>;
export declare function deferredConditional<T>(value: T): Conditional<T>;
export type EventName = `on${Capitalize<Direction>}`;
export type Id = string & { readonly __brand: "Id" };
export type Merged = Point & { z: number };

// --- library types ---
export declare const promise: Promise<Point>;
export declare const map: Map<string, Point>;
export declare const set: Set<number>;
export declare const date: Date;
export declare const regexp: RegExp;
export declare const error: Error;
export declare const bytes: Uint8Array;
export declare const buffer: ArrayBuffer;
export declare const iterable: Iterable<number>;
export declare const asyncIterable: AsyncIterable<string>;
export declare const url: URL;
export declare function fetchLike(input: string, init?: { signal?: AbortSignal }): Promise<Response>;

// --- any, unknown, never ---
export declare function takesAny(value: any): any;
export declare function takesUnknown(value: unknown): unknown;
export declare function fails(message: string): never;
export declare const anyValue: any;
export declare const neverArray: never[];

// --- default export and namespaces ---
export default function main(args: string[]): number { return args.length; }
export namespace Util { export const version = "1"; export function helper(): void {} }

// An optional enum parameter keeps the enum's type.
export function withLevel(level?: Level): Level | null { return level ?? null; }

// Literals next to `string & {}` are suggestions: any string is accepted.
export type Autocapitalize = "none" | "off" | "on" | (string & {});
export function capitalize(mode?: Autocapitalize): void {}

// Classes are cases of a union, told apart with `instanceof`. A subclass
// names its superclass, so it is tested first.
export class Vehicle { constructor(public wheels: number) {} }
export class Car extends Vehicle { honk(): void {} }
export class Boat { sail(): void {} }
export function park(what: Car | Vehicle | string): void {}
export function repair(what: Boat | Vehicle): Boat | Vehicle { return what; }

// `symbol`, and global classes beside one plain object.
export function onEvent(name: string | symbol, target: EventTarget | Map<string, string>): void {}
export function setHeaders(init: Headers | Map<string, string> | Record<string, string>): void {}
export function at(when: Date | number | URL): void {}
export function pet(what: Dog | Animal | null): void {}

// Plain objects told apart by their fields.
export declare function settle(): { result: string } | { error: string; code?: number };
export type Person = { name: string } | { name: string; age: number };
export type Reading = { value: string } | { value: number };
export type Headers2 = { name: string; value: string } | Record<string, string>;
export type Blurred = { x: number } | { x: number; y?: string };
export interface SpotA { x: number; y: number }
export interface SpotB { x: number; y: number }
export type Spot = SpotA | SpotB | string;

// --- names and shapes that once produced declarations that do not compile ---
// A literal that is a ReScript keyword.
export type ReadyState = "open" | "closed" | "in" | "and" | "true";
// A type named like a built-in ReScript type.
export interface Dict<T> { [key: string]: T | undefined }
export declare function env(): Dict<string>;
// A callable library interface is no function type in ReScript.
export declare function listen(callback: EventListener | EventListenerObject | null): void;
// An unnamed member of a generic type has the type's parameters.
export interface Ref<T> { current: T }
export interface RefAttributes<T> { ref?: Ref<T | null> | ((instance: T | null) => void) }
export declare function pick<T>(from: { items: T[] }): T;
// Iterators.
export declare function entries(): IterableIterator<[string, number]>;

// Members that share a tag: the kind of `value` tells the literals apart,
// presence of `optional` the identifiers; two patterns that differ only
// inside `elements` are one case.
export interface StringLit { type: "Literal"; value: string; raw: string | null }
export interface NumericLit { type: "Literal"; value: number; raw: string | null }
export interface IdentName { type: "Identifier"; name: string }
export interface IdentBinding { type: "Identifier"; name: string; optional: boolean }
export interface ArrayPat { type: "ArrayPattern"; elements: (IdentBinding | null)[] }
export interface ArrayTarget { type: "ArrayPattern"; elements: (IdentName | null)[] }
export type SyntaxNode = StringLit | NumericLit | IdentName | IdentBinding | ArrayPat | ArrayTarget;
export declare function visit(node: SyntaxNode): void;

// Merged members whose fields join: literals with their primitive, a type
// with its nullable form, and a merged case with a type parameter.
export interface NamedProp { type: "Prop"; name: string; size: number }
export interface KnownProp { type: "Prop"; name: "width" | "height"; size: number | null }
export interface Other { type: "Other"; id: number }
export interface Third { type: "Third"; label: string }
export interface Fourth { type: "Fourth"; flag: boolean }
export type Prop = NamedProp | KnownProp | Other | Third | Fourth;
export type Holder<T> = { type: "Held"; value: T; note?: string } | { type: "Held"; value: T } | { type: "Empty" };
export declare function hold<T>(value: T): Holder<T>;
export declare function prop(): Prop;

// Literals told apart by the kind of `value`: `typeof null` is "object".
export interface StrLit { type: "Lit"; value: string; raw: string | null }
export interface NumLit { type: "Lit"; value: number; raw: string | null }
export interface BoolLit { type: "Lit"; value: boolean; raw: string | null }
export interface NullLit { type: "Lit"; value: null; raw: "null" | null }
export interface Ident { type: "Ident"; name: string }
export type Lit = StrLit | NumLit | BoolLit | NullLit | Ident;
export declare function lit(): Lit;
