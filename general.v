Require Import HoTT.

Definition curry
           {X Y Z : Type}
           (f : X * Y -> Z)
  : X -> Y -> Z
  := fun x y => f(x, y).

Definition uncurry_ap
           {X Y Z : Type}
           (f : X -> Y -> Z)
           {x₁ x₂ : X} {y₁ y₂ : Y}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : ap (uncurry f) (path_prod' p q)
    =
    ap (fun z => f z y₁) p @ ap (f x₂) q
  := match p, q with
     | idpath, idpath => idpath
     end.

Definition curry_ap
           {X Y Z : Type}
           (f : X * Y -> Z)
           {x₁ x₂ : X * Y}
           (p : x₁ = x₂)
  : ap f p
    =
    (ap (fun z => curry f z (snd x₁)) (ap fst p))
      @ (ap (fun z => curry f (fst x₂) z) (ap snd p))
  := match p with
     | idpath => idpath
     end.

Definition ap_pair_l
           {X Y : Type}
           {x₁ x₂ : X} (y : Y)
           (p : x₁ = x₂)
  : ap (fun x => (x, y)) p = path_prod' p idpath
  := match p with
     | idpath => idpath
     end.

Definition ap_pair_r
           {X Y : Type}
           (x : X) {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : ap (pair x) q = path_prod' idpath q
  := match q with
     | idpath => idpath
     end.
