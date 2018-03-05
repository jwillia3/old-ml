# GRAMMAR
```
aexp    false / true / int / real / string / (exp,...) / [exp,...] / name / fun name...->exp
appexp  aexp... aexp
infexp  appexp [name infexp]
exp     if exp (| pat -> exp)
        if exp then exp else exp
        let name name... = exp in exp
        __op (int name...)... in exp
        letrec (name name... = exp);... in exp
        infexp
apat    false / true / int / real / string / (exp,...) / [exp,...] / name
pat     apat[:pat]
```

# OPERATORS
LEVEL   |   LEFT            |   RIGHT
--------|-------------------|-----------
    9   |                   |
    8   |   * / rem ++      |
    7   |   + -             |   :
    6   |   == /= <= >= < > |   
    5   |                   |   and or
    4   |                   |
    3   |                   |
    2   |                   |
    1   |   >>              |   <<