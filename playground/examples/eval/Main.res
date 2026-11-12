// The JavaScript output has the numbers, and no import of Sieve.
let primes = %Macro.eval(Sieve.primesBelow(60))
let fib25 = %Macro.eval(Sieve.fib(25))
let banner = %Macro.eval(String.repeat("=", 20) ++ " primes " ++ String.repeat("=", 20))

Console.log(banner)
Console.log(primes)
Console.log(fib25)
