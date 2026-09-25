// error-output-parity: template interpolations are parsed as expression blocks
let q = sql`SELECT * FROM ${}`
