export interface Address {
  street: string;
  city: string;
}

export interface User {
  id: string;
  name: string;
  age?: number;
  email: string | null;
  tags: string[];
  address: Address;
}

export async function getUser(id: string): Promise<User | undefined> {
  return undefined;
}

export function rename(user: User, name: string): User {
  return { ...user, name };
}
