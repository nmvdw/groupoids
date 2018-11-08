Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.bicategories.Bicat.

Open Scope cat.

Definition build_bicategory
           (ob : UU)
           (mor : ob -> ob -> UU)
           (cell : ∏ {X Y : ob}, mor X Y -> mor X Y -> UU)
           (id₁ : ∏ (X : ob), mor X X)
           (comp : ∏ {X Y Z : ob}, mor X Y -> mor Y Z -> mor X Z)
           (id₂ : ∏ {X Y : ob} (f : mor X Y), cell f f)
           (vcomp : ∏ {X Y : ob} {f g h : mor X Y}, cell f g -> cell g h -> cell f h)
           (lwhisk : ∏ {X Y Z : ob} (f : mor X Y) {g h : mor Y Z},
                     cell g h -> cell (comp f g) (comp f h))
           (rwhisk : ∏ {X Y Z : ob} {g h : mor X Y} (f : mor Y Z),
                     cell g h -> cell (comp g f) (comp h f))
           (lunitor : ∏ {X Y : ob} (f : mor X Y),
                      cell (comp (id₁ X) f) f)
           (lunitor_inv : ∏ {X Y : ob} (f : mor X Y),
                          cell f (comp (id₁ X) f))
           (runitor : ∏ {X Y : ob} (f : mor X Y),
                      cell (comp f (id₁ Y)) f)
           (runitor_inv : ∏ {X Y : ob} (f : mor X Y),
                          cell f (comp f (id₁ Y)))
           (lassocor : ∏ {W X Y Z : ob} (f : mor W X) (g : mor X Y) (h : mor Y Z),
                       cell (comp f (comp g h)) (comp (comp f g) h))
           (rassocor : ∏ {W X Y Z : ob} (f : mor W X) (g : mor X Y) (h : mor Y Z),
                       cell (comp (comp f g) h) (comp f (comp g h)))
           (vcomp_left : ∏ (X Y : ob) (f g : mor X Y) (α : cell f g),
                          vcomp (id₂ f) α = α)
           (vcomp_right : ∏ (X Y : ob) (f g : mor X Y) (α : cell f g),
                         vcomp α (id₂ g) = α)
           (vcomp_assoc : ∏ (X Y : ob)
                            (f g h k : mor X Y)
                            (α₁ : cell f g) (α₂ : cell g h) (α₃ : cell h k),
                          vcomp α₁ (vcomp α₂ α₃) = vcomp (vcomp α₁ α₂) α₃)
           (lwhisk_id : ∏ (X Y Z : ob) (f : mor X Y) (g : mor Y Z),
                        lwhisk f (id₂ g) = id₂ _)
           (rwhisk_id : ∏ (X Y Z : ob) (f : mor X Y) (g : mor Y Z),
                        rwhisk g (id₂ f) = id₂ _)
           (lwhisk_comp : ∏ (X Y Z : ob)
                            (f : mor X Y) (g h i : mor Y Z)
                            (α : cell g h) (β : cell h i),
                          lwhisk f (vcomp α β) = vcomp (lwhisk f α) (lwhisk f β))
           (rwhisk_comp : ∏ (X Y Z : ob)
                            (f g h : mor X Y) (i : mor Y Z)
                            (α : cell f g) (β : cell g h),
                          rwhisk i (vcomp α β) = vcomp (rwhisk i α) (rwhisk i β))
           (lunitor_natural : ∏ (X Y : ob) (f g : mor X Y) (α : cell f g),
                             vcomp (lwhisk (id₁ _) α) (lunitor g) = vcomp (lunitor f) α)
           (runitor_natural : ∏ (X Y : ob) (f g : mor X Y) (α : cell f g),
                              vcomp (rwhisk (id₁ _) α) (runitor g) = vcomp (runitor f) α)
           (lwhisk_lwhisk : ∏ (W X Y Z : ob)
                              (f : mor W X) (g : mor X Y) (h i : mor Y Z)
                              (α : cell h i),
                            vcomp (lwhisk f (lwhisk g α)) (lassocor f g i)
                            =
                            vcomp (lassocor f g h) (lwhisk _ α))
           (rwhisk_lwhisk : ∏ (W X Y Z : ob)
                              (f : mor W X) (g h : mor X Y) (i : mor Y Z)
                              (α : cell g h),
                            vcomp (lwhisk f (rwhisk i α)) (lassocor f h i)
                            =
                            vcomp (lassocor f g i) (rwhisk i (lwhisk f α)))
           (rwhisk_rwhisk : ∏ (W X Y Z : ob)
                              (f g : mor W X) (h : mor X Y) (i : mor Y Z)
                              (α : cell f g),
                            vcomp (rwhisk _ α) (lassocor _ _ _)
                            =
                            vcomp (lassocor f h i) (rwhisk i (rwhisk h α)))
           (vcomp_whisker : ∏ (X Y Z : ob)
                              (f g : mor X Y) (h i : mor Y Z)
                              (α : cell f g) (β : cell h i),
                            vcomp (rwhisk h α) (lwhisk g β)
                            =
                            vcomp (lwhisk f β) (rwhisk i α))
           (lunitor_left : ∏ (X Y : ob) (f : mor X Y),
                           vcomp (lunitor f) (lunitor_inv f) = id₂ _)
           (lunitor_right : ∏ (X Y : ob) (f : mor X Y),
                            vcomp (lunitor_inv f) (lunitor f) = id₂ _)
           (runitor_left : ∏ (X Y : ob) (f : mor X Y),
                           vcomp (runitor f) (runitor_inv f) = id₂ _)
           (runitor_right : ∏ (X Y : ob) (f : mor X Y),
                            vcomp (runitor f) (runitor_inv f) = id₂ _)
           (lassocor_left : ∏ (W X Y Z : ob)
                              (f : mor W X) (g : mor X Y) (h : mor Y Z),
                            vcomp (lassocor f g h) (rassocor f g h) = id₂ _)
           (lassocor_right : ∏ (W X Y Z : ob)
                               (f : mor W X) (g : mor X Y) (h : mor Y Z),
                             vcomp (rassocor f g h) (lassocor f g h) = id₂ _)
           (triangle : ∏ (X Y Z : ob) (f : mor X Y) (g : mor Y Z),
                       vcomp (lassocor f (id₁ Y) g) (rwhisk g (runitor f))
                       =
                       lwhisk f (lunitor g))
           (pentagon : ∏ (V W X Y Z : ob)
                         (f : mor V W) (g : mor W X) (h : mor X Y) (k : mor Y Z),
                       vcomp (lassocor f g (comp h k)) (lassocor (comp f g) h k)
                       =
                       vcomp (vcomp (lwhisk f (lassocor g h k)) (lassocor _ _ _))
                                    (rwhisk k (lassocor _ _ _))
           )
  : bicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * use tpair.
        ** use tpair.
           *** exact (tpair (λ ob, ob -> ob -> UU) ob mor).
           *** use tpair.
               **** exact id₁.
               **** exact comp.
        ** exact cell.
      * use tpair.
        ** exact id₂.
        ** repeat (use tpair) ; simpl.
           *** exact lunitor.
           *** exact runitor.
           *** exact lunitor_inv.
           *** exact runitor_inv.
           *** exact rassocor.
           *** exact lassocor.
           *** exact vcomp.
           *** exact lwhisk.
           *** exact rwhisk.
    + simpl ; unfold prebicat_laws.