Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     examples.terminal
     examples.precat
     examples.lax_functors_bicat.
From GR.bicategories.lax_functor Require Import
     lax_functor.

Section Monad.
  Context `{Univalence}.
  Variable (C : BiCategory).

  Definition monad := Lax terminal_bicategory C.

  Section MonadData.
    Variable (m : monad).
    
    Definition under_m :  C
      := Fobj m tt.

    Definition endo_m : C⟦under_m,under_m⟧
      := Fmor m tt tt tt.

    Definition unit : id₁ under_m ==> endo_m
      := Fid m tt.

    Definition bind : endo_m · endo_m ==> endo_m
      := Fcomp m tt tt tt (tt,tt).

    Definition bind_unit
      : bind ∘ (unit ◅ endo_m) ∘ left_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_l ; cbn.
      rewrite <- left_unit_left.
      f_ap.
      rewrite left_unit_left.
      rewrite (@F_left_unit _ _ m tt tt tt).
      assert (m ₂ (@left_unit terminal_bicategory tt tt tt) = id₂ _) as ->.
      {
        cbn.
        rewrite <- (@Fmor₂_id₂ terminal_bicategory C m tt tt tt).
        reflexivity.
      }
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition unit_bind
      : bind ∘ (endo_m ▻ unit) ∘ right_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_r ; cbn.
      rewrite <- right_unit_left.
      f_ap.
      rewrite right_unit_left.
      rewrite (@F_right_unit _ _ m tt tt tt).
      assert (m ₂ (@right_unit terminal_bicategory tt tt tt) = id₂ _) as ->.
      {
        cbn.
        rewrite <- (@Fmor₂_id₂ terminal_bicategory C m tt tt tt).
        reflexivity.
      }
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition bind_bind
      : bind ∘ (bind ◅ endo_m)
        =
        bind ∘ (endo_m ▻ bind) ∘ assoc endo_m endo_m endo_m.
    Proof.
      unfold bind, endo_m, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite F_assoc.
      cbn.
      f_ap.
      rewrite (@Fmor₂_id₂ terminal_bicategory C m tt tt tt).
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.
  End MonadData.
End Monad.