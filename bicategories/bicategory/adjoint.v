Require Import HoTT.
From GR.bicategories Require Import general_category bicategory.bicategory equivalence.

Local Open Scope bicategory_scope.

Record is_adjunction
       `{Univalence}
       {C : BiCategory}
       {X Y : C}
       (l : one_cell X Y)
       (r : one_cell Y X)
  := {
      unit : two_cell (id_m X) (c_m (r,l)) ;
      counit : two_cell (c_m (l,r)) (id_m Y) ;
      unit_counit_l : ((un_r _ _ r)
                       o (((bc_whisker_r (id_m Y) r counit)
                       o (assoc (r,l,r)))
                       o (bc_whisker_l r (r ⋅ l) unit))
                       o ((un_l Y X r)^-1))%morphism
                      = 1%morphism ;
      unit_counit_r : ((un_l _ _ l)
                         o (((bc_whisker_l l _ counit)
                         o ((assoc (l,r,l))^-1))
                         o (bc_whisker_r _ l unit))
                         o (un_r X Y l)^-1)%morphism
                      = 1%morphism                         
    }.

Arguments unit {_ C X Y l r}.
Arguments counit {_ C X Y l r}.
Arguments unit_counit_l {_ C X Y l r}.
Arguments unit_counit_r {_ C X Y l r}.

Record adjunction
       `{Univalence}
       {C : BiCategory}
       (X Y : C)
  := {
      left_adj : one_cell X Y ;
      right_adj : one_cell Y X ;
      adj_isadj : is_adjunction left_adj right_adj
    }.