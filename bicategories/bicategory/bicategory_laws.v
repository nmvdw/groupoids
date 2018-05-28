Require Import HoTT.
From HoTT.Categories Require Export
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.

Section laws.
  Context `{Univalence}.
  Variable (C : BiCategory).

  Definition triangle_l
             {x y z : C}
             (g : Hom C y z) (f : Hom C x y)
    : (@morphism_of _
                    _
                    c_m
                    (c_m (g,id_m y),f)
                    (g,f)
                    ((un_r y z) g, 1)
        o (assoc (g, id_m y, f))^-1
      =
      (@morphism_of _
                    _
                    c_m
                    (g,c_m (id_m y,f))
                    (g,f)
                    (1,un_l x y f)))%morphism.
  Proof.
    refine (ap (fun z => z o _) (triangle_r C x y z g f) @ _)%morphism.
    refine (associativity _ _ _ _ _ _ _ _ @ _).
    exact (ap (fun z => _ o z) right_inverse @ right_identity _ _ _ _)%morphism.
  Defined.
End laws.