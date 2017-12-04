##A FCL specializer -- a path to enlightenment,

- [fcl-interpreter.scm](fcl-interpreter.scm) -- self-explanatory
``operational'' semantics of basic FCL, and Gluck's FCL* (FCL extended
with calls.

- [1--FCL-interpreter.scm](1--FCL-interpreter.scm) -- naive, ``tendentional''
implementation of FCL...

- [2--FCL-online-specializer.scm](2--FCL-online-specializer.scm) -- homomorphic
to previous one, online specializer for fcl. mind it does not terminate on
certain inputs!

- [3--FCL-interpreter-compressing-transitions.scm](3--FCL-interpreter-compressing-transitions.scm) -- as (1), only ``tail-call
  optimized''...

- [4--FCL-online-specializer-compressing-transitions.scm](4--FCL-online-specializer-compressing-transitions.scm) -- as (2) but as in (3) with ``tail-call optimizaton'',
i.e. in transitions compression on-the-fy. mind it still does not terminate
on certain inputs.

- [5--FCL-online-specializer-comp.transitions+gen.scm](5--FCL-online-specializer-comp.transitions+gen.scm) -- THIS ONE is *different*. it always terminates (provided
the target program does terminate on all possible inputs...). a very simple attempt
at generalization-as-forgetting-static-values.


todo:

- partially-static datastructures
- calls [FCL*] ?
- ...
