// The JavaScript output has the numbers, and no import of Sieve.
let primes = %comptime(Sieve.primesBelow(60))
let fib25 = %comptime(Sieve.fib(25))
let banner = %comptime(String.repeat("=", 20) ++ " primes " ++ String.repeat("=", 20))

Console.log(banner)
Console.log(primes)
Console.log(fib25)
