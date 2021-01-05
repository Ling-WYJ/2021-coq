### Tactics

#### apply

要使用apply策略，要apply的（结论）必须与目标完全匹配-例如，如果相等的左右两侧互换，apply将不起作用。

##### apply with

无法匹配时需要指定来显式调用实例

```
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.
```



#### symmetry

如果我们不能使用apply策略，我们可以先用symmetry交换左右两边。

#### transitivity

目的与apply trans_eq 相同；需要声明所需的实例化

```
Example trans_eq_example'' : ∀ (a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.
```

#### injection

通过在这一点上写入`injection`H作为HMN，我们要求Coq的生成所有方程，它可以选自H使用构造的注入（在本例中，公式N = M）推断。 每一个这样的方程被添加作为一个假设（在这种情况下，名称HMN）插入上下文。

```
Theorem S_injective' : ∀ (n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.
```

```
Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.
```

#### discriminate

荒谬假设无法相等

```
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. discriminate H.
Qed.
```

```
Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

```

##### f_equal

```
Theorem f_equal : ∀ (A B : Type) (f: A → B) (x y: A),
  x = y → f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
```

##### eq_implies_succ_equal

```
Theorem eq_implies_succ_equal : ∀ (n m : nat),
    n = m → S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.
```

#### simpl in H

在假设H中执行simpl.

##### s_inj

```
Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.
```

#### symmetry in H

```
Theorem silly3' : ∀ (n : nat),
  (n =? 5 = true → (S (S n)) =? 7 = true) →
  true = (n =? 5) →
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.
```

##### double_injective

仅仅引入n，这样放宽了条件，证明起来更方便

```
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
```

##### plus_n_n_injective

```
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
```

#### generalize dependent

首先引入所有量化的变量，然后重新概括其中的一个或多个变量，有选择地将变量移出上下文，然后将其放回到目标的开始。

##### plus_n_n_injective

```
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intro n. induction n as [| n' IH].
  - intros m e. destruct m as [| m'].
    + reflexivity.
    + discriminate e. 
  - intros m e. destruct m as [| m'].
    + discriminate e.
    + apply f_equal. apply IH. 
      simpl in e. rewrite <- plus_n_Sm in e. 
      rewrite <- plus_n_Sm in e. injection e as goal.
      apply goal.
Qed.
```

##### nth_error_after_last

```
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
```

#### unfold

#### Destruct on compound expressions

如果e是其类型是某种归纳定义的类型T的表达式，则对于T的每个构造函数c，destruct e都会生成一个子目标，其中所有e出现（在目标和上下文中）都被c替换。可以对子式进行命名，比如 destruct (n =? 3) eqn:Heqe3. 类似Heqe3 : (n =? 3) = false
Heqe5 : (n =? 5) = false。这样可以更灵活。

```
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

```

此处destruct n =? 3以及n =? 5整个式子的真假值。

##### combine_split（看一下proof）

```
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
```

