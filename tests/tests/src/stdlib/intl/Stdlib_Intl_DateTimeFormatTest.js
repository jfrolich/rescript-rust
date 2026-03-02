console.log()("---");

console.log()("Intl.DateTimeFormat");

(prim => {
  
  
})(Intl.DateTimeFormat.supportedLocalesOf()("None", ["en-US", "en-GB"]));

(prim => {
  
  
})(Intl.DateTimeFormat.supportedLocalesOf()({TAG: "Some", _0: {localeMatcher: "lookup"}}, ["en-US", "en-GB"]));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: {TAG: "Some", _0: "full"}, timeStyle: {TAG: "Some", _0: "full"}, calendar: "None", dayPeriod: "None", numberingSystem: "None", localeMatcher: "None", timeZone: "None", hour12: "None", hourCycle: "None", formatMatcher: "None", weekday: "None", era: "None", year: "None", month: "None", day: "None", hour: "None", minute: "None", second: "None", fractionalSecondDigits: "None", timeZoneName: "None"}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

console.log()(formatRange()(Date()(31, 12, 2023), Date()(1, 1, 2023), formatter));

let options = {dateStyle: "None", timeStyle: "None", calendar: "None", dayPeriod: "None", numberingSystem: "None", localeMatcher: "None", timeZone: {TAG: "Some", _0: "UTC"}, hour12: {TAG: "Some", _0: false}, hourCycle: {TAG: "Some", _0: "h24"}, formatMatcher: "None", weekday: {TAG: "Some", _0: "narrow"}, era: {TAG: "Some", _0: "narrow"}, year: {TAG: "Some", _0: "2-digit"}, month: {TAG: "Some", _0: "2-digit"}, day: {TAG: "Some", _0: "2-digit"}, hour: {TAG: "Some", _0: "2-digit"}, minute: {TAG: "Some", _0: "2-digit"}, second: {TAG: "Some", _0: "2-digit"}, fractionalSecondDigits: {TAG: "Some", _0: "3"}, timeZoneName: {TAG: "Some", _0: "longGeneric"}};

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: options}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: options.dateStyle, timeStyle: options.timeStyle, calendar: options.calendar, dayPeriod: options.dayPeriod, numberingSystem: options.numberingSystem, localeMatcher: options.localeMatcher, timeZone: options.timeZone, hour12: options.hour12, hourCycle: options.hourCycle, formatMatcher: options.formatMatcher, weekday: options.weekday, era: options.era, year: options.year, month: options.month, day: options.day, hour: options.hour, minute: options.minute, second: options.second, fractionalSecondDigits: options.fractionalSecondDigits, timeZoneName: {TAG: "Some", _0: "long"}}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: options.dateStyle, timeStyle: options.timeStyle, calendar: options.calendar, dayPeriod: options.dayPeriod, numberingSystem: options.numberingSystem, localeMatcher: options.localeMatcher, timeZone: options.timeZone, hour12: options.hour12, hourCycle: options.hourCycle, formatMatcher: options.formatMatcher, weekday: options.weekday, era: options.era, year: options.year, month: options.month, day: options.day, hour: options.hour, minute: options.minute, second: options.second, fractionalSecondDigits: options.fractionalSecondDigits, timeZoneName: {TAG: "Some", _0: "longOffset"}}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: options.dateStyle, timeStyle: options.timeStyle, calendar: options.calendar, dayPeriod: options.dayPeriod, numberingSystem: options.numberingSystem, localeMatcher: options.localeMatcher, timeZone: options.timeZone, hour12: options.hour12, hourCycle: options.hourCycle, formatMatcher: options.formatMatcher, weekday: options.weekday, era: options.era, year: options.year, month: options.month, day: options.day, hour: options.hour, minute: options.minute, second: options.second, fractionalSecondDigits: options.fractionalSecondDigits, timeZoneName: {TAG: "Some", _0: "short"}}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: options.dateStyle, timeStyle: options.timeStyle, calendar: options.calendar, dayPeriod: options.dayPeriod, numberingSystem: options.numberingSystem, localeMatcher: options.localeMatcher, timeZone: options.timeZone, hour12: options.hour12, hourCycle: options.hourCycle, formatMatcher: options.formatMatcher, weekday: options.weekday, era: options.era, year: options.year, month: options.month, day: options.day, hour: options.hour, minute: options.minute, second: options.second, fractionalSecondDigits: options.fractionalSecondDigits, timeZoneName: {TAG: "Some", _0: "shortGeneric"}}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let formatter = Intl.DateTimeFormat()({TAG: "Some", _0: {dateStyle: options.dateStyle, timeStyle: options.timeStyle, calendar: options.calendar, dayPeriod: options.dayPeriod, numberingSystem: options.numberingSystem, localeMatcher: options.localeMatcher, timeZone: options.timeZone, hour12: options.hour12, hourCycle: options.hourCycle, formatMatcher: options.formatMatcher, weekday: options.weekday, era: options.era, year: options.year, month: options.month, day: options.day, hour: options.hour, minute: options.minute, second: options.second, fractionalSecondDigits: options.fractionalSecondDigits, timeZoneName: {TAG: "Some", _0: "shortOffset"}}}, "None");

console.log()(format()(Date()(Date.now()("()")), formatter));

let resolvedOptions = resolvedOptions()(Intl.DateTimeFormat()("None", "None"));

let record = resolvedOptions;

let timeZone = record.timeZone;