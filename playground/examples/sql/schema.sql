create table customers (
  id integer primary key,
  name text not null,
  city text,
  vip boolean not null
);

create table orders (
  id integer primary key,
  customer_id integer not null references customers(id),
  total numeric not null,
  shipped_at timestamp
);
