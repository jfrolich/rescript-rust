module Length = %Units.table("meters", [("feet", 0.3048), ("miles", 1609.344)])

@Trace.calls
let marathon = (miles: float) => Length.milesToMeters(miles) /. 1000.0

Console.log(marathon(26.219))
Console.log(Length.metersToFeet(100.0))
