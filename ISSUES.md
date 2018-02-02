This file collects on-going issues and enhancements for the `tct-trs` module.
Further problems and improvements about the overall behaviour are discussed in
the `tct-core` module.

### * matchbounds: result depends on rule order #bug #minor

The successful application of the `bounds` processor depends on the order of
the rules. 

Following example is solved by _tct2_ but not by _tct3_:

```
(VAR x y )
(RULES 
   f(c(s(x),y)) -> f(c(x,s(y)))
   g(c(x,s(y))) -> g(c(s(x),y))
   g(s(f(x))) -> g(f(x))
)
```

Note that the internal representation of rules differ.

When we rename `s` to `a` then (the `ruleList`) representation of the tools
coincide, and the problem is not solved by any of the tools.

```
(VAR x y )
(RULES 
    f(c(a(x),y)) -> f(c(x,a(y)))
    g(a(f(x))) -> g(f(x))
    g(c(x,a(y))) -> g(c(a(x),y))
)
```

It seems that the application depends on which order rules are processed. It
has to be clarified if we can generalize the proof search such that it is order
independent. 

Nonetheless, so far all applications in the certified strategy on the tpdb have
been certified successfully.



### * alternative DP graph estimation #enhancement #minor

Current implementation is based on `tcap/icap`. TcT2 uses `icap*`. AY and CS
are investigating other alternatives.



### * alternative usable rules estimation #enhancement #minor

The `usableRules` processor is currently more restrictive than _CeTA_, which allows
- usable rules for non-`DP` problems
- uses `icap` and `usableSymbols` (which are incomparable) for estimating usable rules.



### * pop* processor #enhancement #major

Port `pop*` form `TcT2`.



### * uncurry processor #enhancement #minor

Port `uncurry` form `TcT2`.



### * inlining #enhancement #major

The `AProVE` strategy heavily relies on `narrowing` which seems to be
particularly beneficial in some translated examples where constraints have been
encoded. MA has implemented `narrowing/inlining`, which is already used for
`decreasingLoops` processor. `Narrowing/inlining` can be defined as a processor
for innermost runtime.



### * RaML Strategy #enhancement #major

MA used a dedicate Strategy for RaML examples. The termcomp strategy up to 2016
does not make use of this strategy. For termcomp 2017 GM implemented a simple greedy
strategy.
Besides  `pop*` everything that is used in the RaML strategy is implemented 
The strategy should be ported and tested.



### * incorporate GUBS/heuristics #enhancement #minor

Preliminary tests show practicability of `GUBS` for polynomial interpretations.
In particular the certification strategy could benefit from it. `GUBS` allows
to easily implement heuristics without breaking soundness. For example, one
simple heuristics is to fix the interpretation for constructor symbols. Though
incomplete, in this case `GUBS` can simplify the problems significantly. Note
that `GUBS` provides means for decomposition even when the problem is not a DP
problem. It could be interesting to explore dedicated strategies for
simplifying, decomposing polynomial interpretations.



### * better defaults #minor #ui

Derivational complexity is used per default. Should probably be Runtime
Innermost.



### * update dependencies to recent ghc/stackage version

Building all packages is getting instable due to package conflicts. Update
dependencies.


