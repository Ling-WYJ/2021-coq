### Indprop

#### ev

##### ev

```
Inductive ev : nat → Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

##### ev_4

```
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
```

##### ev_double

```
Theorem ev_double : forall n,
  ev (double n).
```

##### ev_inversion(注意证明)

```
Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
```

##### ev_minus2（注意证明）

```
Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.
```

##### evSS_ev

```
Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
```

##### one_not_even

```
Theorem one_not_even : ~ ev 1.
```

##### SSSSev__even

```
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
```

##### ev5_nonsense （注意inversion用法）

```
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
intros E. inversion E as[|n1 E1].
 inversion E1 as [|n2 E2].
 inversion E2.
Qed.
```

##### ev_even

```
Lemma ev_even : forall n,
  ev n -> even n.
```

##### ev_even_iff

```
Theorem ev_even_iff : forall n,
  ev n <-> even n.
```

#####  ev_sum 

```
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
```

#####  ev_ev__ev 

```
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
```

#### le

##### le（ <= ）

```
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
```

##### le_trans

```
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
```

##### O_le_n

```
Theorem O_le_n : forall n,
  0 <= n.
```

##### n_le_m__Sn_le_Sm

```
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
```

##### Sn_le_Sm__n_le_m 

```
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
```

##### le_plus_l

```
Theorem le_plus_l : forall a b,
  a <= a + b.
```



#### lt

##### lt( < )

```
Definition lt (n m:nat) := le (S n) m.
```

