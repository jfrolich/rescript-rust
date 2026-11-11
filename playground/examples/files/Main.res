let title: string = %I18n.t("title")
let greet = %I18n.t("greeting")

Console.log(title)
Console.log(greet(~name="Alice", ~count="3"))

// A key that is not in en.json does not compile:
// let oops = %I18n.t("goodbye")
