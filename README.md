# Constructive Finite Pigeon Hole Proof

Coq proof of

```coq
Theorem pigeonhole_principle:
  forall (X:Type) (l1 l2: list X),
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
```

The idea of the proof is that while equality may not be decidable over type X, equality is decidable over natural integers. Thus, one can inject elements of list l1 into naturals via the index of the element it corresponds to in l2. 
The list of indices is repetitive and thus implies the original list also is.