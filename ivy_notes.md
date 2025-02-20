Syntax:
1. Types, relations, individuals and actions cannot begin with a capital letter

e.g. `action step ...` is not allowed but `action Step ...` is not

2. Arguments when declaring variables must begin with a capital letter

e.g. `relation r(N: ...` is allowed but `relation r(n: ...` is not

3. Arguments of actions must not begin with a capital letter

e.g. `action step(n: ...` is allowed but `action step(N: ...` is not

3. Negative numbers and BODMAS (including brackets) cannot be in ranges or explicit sorts

e.g. `type n = {-1}` and `type n = {(1 + 1)}` are not allowed

4. Semi colons after every line should be added

5. Functions are immutable and so relations should be used

6. IVy expresses everything in first order logic so arithmetic cannot be defined. Thresholds for broadcast protocols were worked out through properties about intersection.

SWISS Problems:
- The language is 1.5 so keywords such as `require` are not allowed
- The only allowed types are uninterpreted, bool and function sorts (no interpreted sorts)