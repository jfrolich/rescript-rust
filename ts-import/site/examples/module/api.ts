export interface Todo {
  id: number;
  title: string;
  done: boolean;
}

export type Filter = "all" | "active" | "done";

export enum Priority {
  Low,
  Normal,
  High,
}

export function list(filter: Filter): Promise<Todo[]> {
  return Promise.resolve([]);
}

export function create(title: string, priority?: Priority): Promise<Todo> {
  return Promise.resolve({ id: 1, title, done: false });
}

export const pageSize = 20;
