---
title: Scala's syntax
date: 2013-03-26
---

I’m studying a bit of Scala.  I find the syntax even more amusing than the rest
of the language:

> In the expression '1 :: twoThree', :: is a method of its right operand, the
> list, twoThree. You might suspect there’s something amiss with the
> associativity of the :: method, but it is actually a simple rule to remember:
> If a method is used in operator notation, such as a * b, the method is invoked
> on the left operand, as in a.*(b)---unless the method name ends in a colon. If
> the method name ends in a colon, the method is invoked on the right
> operand. Therefore, in 1 :: twoThree, the :: method is invoked on twoThree,
> passing in 1, like this: twoThree.::(1). [^1]

Which is a great example of ramming through the [principle of least
astonishment](https://en.wikipedia.org/wiki/Principle_of_least_astonishment)---although
it is a somewhat nice shorthand, I can only imagine the confusion if you are
unfortunate enough not to know.

It is interesting that in GHC Haskell colons are special too: type operators
must start with one.  In that case however the surprise comes only when trying
to *define* a type operator, which is much better.

You can also visit <http://scalapuzzlers.com> for more Scala fun.

[^1]: From 'Programming in Scala, Second Edition'.
