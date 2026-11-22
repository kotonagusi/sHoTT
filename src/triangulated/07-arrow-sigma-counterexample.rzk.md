# A counterexample to the old arrow Σ premise

Take the covariant family supported at the final vertex, and take the second
family to be the constant realized interval. A global section of the first
family would give a point in its empty initial fiber. This discharges the old
sectionwise premise for the second family.

```rzk
#lang rzk-1

#def counter-A (i : 𝕀) : U := Shape 1 (\ _ → i ≡ 1₂)

#def counter-A-cov (funext : FunExt) (weakfunext : WeakFunExt) (extext : ExtExt)
  : is-covariant-arrow-II counter-A
  := is-covariant-arrow-is-a-cov funext weakfunext counter-A
       (\ i → is-a-cov-i===0 funext weakfunext extext i)

#def counter-B-premise (s : (i : 𝕀) → counter-A i)
  : is-covariant-arrow-II (\ _ → ⌈𝕀⌉)
  := match (s 0₂) (point a ⇒ recBOT)
```

If the sum were covariant, its final fiber would be discrete. The interval
arrow in the second coordinate would then give a path between its endpoints.
Projecting that path would identify the endpoints of the realized interval.

```rzk
#def counter-total (i : 𝕀) : U := Σ (a : counter-A i) , ⌈𝕀⌉

#def counter-conclusion-implies-any
  (cov-total : is-covariant-arrow-II counter-total) (Z : U) : Z
  :=
    let X := counter-total 1₂ in
    let a : counter-A 1₂ := point 1 (\ _ → 1₂ ≡ 1₂) *₁ in
    let x : X := (a , pt-⌈𝕀⌉ 0₂) in
    let y : X := (a , pt-⌈𝕀⌉ 1₂) in
    let discrete : is-discrete-II X :=
      is-discrete-is-covariant-II ⌈𝕀⌉
        (equiv-ext-shape-family-fwd 𝕀 □¹ counter-total) cov-total (pt-⌈𝕀⌉ 1₂) in
    let p : x = y := first (first (discrete x y)) (\ t → (a , pt-⌈𝕀⌉ t)) in
    let q := ap X ⌈𝕀⌉ x y (\ w → second w) p in
    match (shape-at-1-of-eq-form-1 (pt-⌈𝕀⌉ 0₂) q) (point witness ⇒ recBOT)
```

Taking the former signature of `is-covariant-arrow-II-Σ` as an argument
therefore gives a term of any type `Z`.

```rzk
#def old-arrow-sigma-implies-any
  (funext : FunExt) (weakfunext : WeakFunExt) (extext : ExtExt)
  (old-rule : (A : 𝕀 → U) → (B : (i : 𝕀) → A i → U) →
    is-covariant-arrow-II A →
    ((s : (i : 𝕀) → A i) → is-covariant-arrow-II (\ i → B i (s i))) →
    is-covariant-arrow-II (\ i → Σ (a : A i) , B i a))
  (Z : U) : Z
  := counter-conclusion-implies-any
       (old-rule counter-A (\ _ _ → ⌈𝕀⌉)
         (counter-A-cov funext weakfunext extext) counter-B-premise) Z
```
