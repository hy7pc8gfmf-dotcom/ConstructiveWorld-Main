open BinInt
open BinNums
open Datatypes
open Nat
open QArith_base
open Qabs
open Qminmax
open S01_BaseRing
open S02_CauchyComplete
open S03_QExp
open S07_RealSetoidExpLog
open S08_RealMainlineDPO
open S09_EntropyReal
open S10_KVQuantTrig
open S11_TP3B5
open S12_B5RecycleSF
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val b5d1_b3rr_atan_deriv_lin :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
    (coq_Real, (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') ->
    coq_Real -> real_lt -> real_le) coq_And) sigT **)

let b5d1_b3rr_atan_deriv_lin r x hxb eps heps =
  let cr =
    b3rr_C2
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
        (coq_Qplus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r))
  in
  let k =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
        Coq_xH }
        (coq_Qplus cr { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let rk = real_const k in
  let hrk_pos = real_const_pos_f1 k in
  let delta =
    real_min
      (real_const
        (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
          (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r)))
      (real_mult eps rk)
  in
  Coq_existT (delta, (Coq_pair
  ((real_min_pos
     (real_const
       (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
         (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r)))
     (real_mult eps (real_const k))
     (real_const_pos_f1
       (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
         (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r)))
     (real_mult_positive eps (real_const k) heps hrk_pos)),
  (fun h hh hxh eps' heps' -> Coq_inl
  (let Coq_existT (_, a) = heps in
   let Coq_pair (_, s) = a in
   let Coq_existT (x0, _) = s in
   let Coq_existT (x1, a0) = heps' in
   let Coq_pair (_, s0) = a0 in
   let Coq_existT (x2, _) = s0 in
   let hh_l =
     real_min_lt_l h
       (real_const
         (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
           (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r)))
       (real_mult eps rk) hh
   in
   let hh_r =
     real_min_lt_r h
       (real_const
         (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
           (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } r)))
       (real_mult eps rk) hh
   in
   let Coq_existT (_, a1) = hh_l in
   let Coq_pair (_, s1) = a1 in
   let Coq_existT (x3, _) = s1 in
   let Coq_existT (_, a2) = hh_r in
   let Coq_pair (_, s2) = a2 in
   let Coq_existT (x4, _) = s2 in
   let s3 =
     real_inv_proj (real_plus real_one (real_mult x x))
       (b3r_one_sq_real_pos x)
   in
   let Coq_existT (x5, _) = s3 in
   let s4 =
     b3rr_qdecay r
       (coq_Qmult x1
         (coq_Qinv { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
   in
   let Coq_existT (x6, _) = s4 in
   let eta =
     coq_Qmult x1
       (coq_Qinv { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
   in
   let heta_pos =
     coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
       (coq_Qmult x1
         (coq_Qinv { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
   in
   Coq_existT (eta, (Coq_pair (heta_pos, (Coq_existT
   ((PeanoNat.Nat.max
      (PeanoNat.Nat.max (PeanoNat.Nat.max x0 x2) (PeanoNat.Nat.max x3 x4))
      (PeanoNat.Nat.max x5 x6)),
   (fun n _ ->
   let wreal =
     real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)
   in
   coq_Qlt_to_QltT eta
     (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1
         (real_abs
           (real_plus (cauchy_real_arctan (real_plus x h) hxh)
             (real_opp
               (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxb))
                 (real_mult h wreal)))))
         n)))))))))))))

(** val b5dD_atan_deriv_b5a_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
    (coq_Real, (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') ->
    coq_Real -> real_lt -> real_le) coq_And) sigT **)

let b5dD_atan_deriv_b5a_r_exp r x hxr eps heps =
  let s = b5d1_b3rr_atan_deriv_lin r x hxr eps heps in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  Coq_existT (x0, (Coq_pair (r0, (fun h hh hxh eps' heps' ->
  let i3 =
    real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)
  in
  let i5 =
    real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)
  in
  let hinv =
    b5c_inv_pos_cert_eq (real_plus real_one (real_mult x x))
      (b5a_one_plus_sq_pos x) (b3r_one_sq_real_pos x)
  in
  let hsl =
    real_eq_trans (real_mult i5 h) (real_mult h i5) (real_mult h i3)
      (real_mult_comm i5 h)
      (RealSetoid.real_eq_mult_compat h i5 h i3 (real_eq_refl h) hinv)
  in
  RealSetoid.real_le_compat
    (real_abs
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3)))))
    (real_abs
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h)))))
    (real_plus (real_mult eps (real_abs h)) eps')
    (real_plus (real_mult eps (real_abs h)) eps')
    (RealSetoid.real_eq_abs_compat
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3))))
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h))))
      (RealSetoid.real_eq_plus_compat
        (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3)))
        (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h)))
        (real_eq_refl (cauchy_real_arctan (real_plus x h) hxh))
        (RealSetoid.real_eq_opp_compat
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3))
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h))
          (RealSetoid.real_eq_plus_compat
            (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)) (real_mult h i3)
            (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)) (real_mult i5 h)
            (real_eq_refl (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)))
            (real_eq_sym (real_mult i5 h) (real_mult h i3) hsl)))))
    (real_eq_refl (real_plus (real_mult eps (real_abs h)) eps'))
    (r1 h hh hxh eps' heps')))))

(** val b5dD_vdh_pts_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt -> coq_Q
    -> coq_Q -> coq_QltT -> coq_QltT -> (coq_Real, (real_lt, coq_Real ->
    real_lt -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (nat, __) sigT)
    coq_And) sigT **)

let b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2 hk2p =
  let hx = b3rr_dom_r1 x r hxr in
  let eps2 = real_mult eps (real_const k2) in
  let heps2 =
    real_mult_positive eps (real_const k2) heps (real_const_pos k2 hk2)
  in
  let s = b5dD_atan_deriv_b5a_r_exp r x hxr eps2 heps2 in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  Coq_existT (x0, (Coq_pair (r0, (fun h hh_UU03b4_ hxh eps' heps' ->
  let eps2' = real_mult eps' (real_const k2p) in
  let heps2' =
    real_mult_positive eps' (real_const k2p) heps' (real_const_pos k2p hk2p)
  in
  let v =
    real_plus (cauchy_real_arctan (real_plus x h) hxh)
      (real_opp
        (real_plus (cauchy_real_arctan x hx)
          (real_mult
            (real_inv_pos (real_plus real_one (real_mult x x))
              (b5a_one_plus_sq_pos x))
            h)))
  in
  let habs = r1 h hh_UU03b4_ hxh (real_mult eps' (real_const k2p)) heps2' in
  let s0 =
    b5i_abs_le_pointwise v (real_plus (real_mult eps2 (real_abs h)) eps2')
      habs eps2' heps2'
  in
  let Coq_existT (x1, _) = s0 in Coq_existT (x1, __)))))

(** val b5dM_real_const_pos : coq_Q -> coq_QltT -> real_lt **)

let b5dM_real_const_pos c _ =
  Coq_existT
    ((coq_Qdiv c { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }),
    (Coq_pair
    ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
       (coq_Qdiv c { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })),
    (Coq_existT (O, (fun n _ ->
    coq_Qlt_to_QltT
      (coq_Qdiv c { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (coq_Qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val b5dM_b5i_one_plus_eps2_pos :
    coq_Real -> coq_Q -> real_lt -> coq_QltT -> real_lt **)

let b5dM_b5i_one_plus_eps2_pos eps k2 heps _ =
  let Coq_existT (_, a) = heps in
  let Coq_pair (_, s) = a in
  let Coq_existT (x, _) = s in
  Coq_existT ({ coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) },
  (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
     Coq_xH); coq_Qden = (Coq_xO Coq_xH) }),
  (Coq_existT (x, (fun n _ ->
  coq_Qlt_to_QltT { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
    (coq_Qminus
      (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
      (projT1 real_zero n))))))))

(** val b5dM_b5n_eps_proj_lt :
    coq_Real -> real_lt -> (coq_Q, (coq_QltT, (nat, __) sigT) coq_And) sigT **)

let b5dM_b5n_eps_proj_lt _ = function
| Coq_existT (x, a) ->
  let Coq_pair (q, s) = a in
  let Coq_existT (x0, _) = s in
  Coq_existT (x, (Coq_pair (q, (Coq_existT (x0, __)))))

(** val b5dM_b5c_d_proj_le_one : coq_Real -> (nat, __) sigT **)

let b5dM_b5c_d_proj_le_one _ =
  Coq_existT (O, __)

(** val b5dI_inv_leaf_witness_eq :
    coq_Real -> coq_Q -> real_lt -> coq_QltT -> real_eq **)

let b5dI_inv_leaf_witness_eq eps k2 heps hk2 =
  RealSetoid.real_eq_mult_compat
    (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      Coq_xH)) })
    (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
      (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2))
    (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      Coq_xH)) })
    (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
      (b5i_one_plus_eps2_pos eps k2 heps hk2))
    (real_eq_refl
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) }))
    (real_inv_pos_ext (real_plus real_one (real_mult eps (real_const k2)))
      (real_plus real_one (real_mult eps (real_const k2)))
      (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2)
      (b5i_one_plus_eps2_pos eps k2 heps hk2)
      (real_eq_refl (real_plus real_one (real_mult eps (real_const k2)))))

(** val b5dI_real_mult_positive_exp :
    coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt **)

let b5dI_real_mult_positive_exp a b ha hb =
  let Coq_existT (x, a0) = ha in
  let Coq_pair (_, s) = a0 in
  let Coq_existT (x0, _) = s in
  let Coq_existT (x1, a1) = hb in
  let Coq_pair (_, s0) = a1 in
  let Coq_existT (x2, _) = s0 in
  Coq_existT ((coq_Qmult x x1), (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } (coq_Qmult x x1)),
  (Coq_existT ((PeanoNat.Nat.max x0 x2), (fun n _ ->
  coq_Qlt_to_QltT (coq_Qmult x x1)
    (coq_Qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val b5dI_sin_atan_diff_closed_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
    coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
    (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real ->
    real_lt -> real_le) coq_And) sigT **)

let b5dI_sin_atan_diff_closed_r_exp r x hxr ms mc c4 _ _ eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let s = coq_Qplus ms mc in
  let k1e =
    coq_Qplus
      (coq_Qmult ms
        (coq_Qplus
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
            Coq_xH } c4)
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (coq_Qmult mc
        (coq_Qplus
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
            Coq_xH } c4)
          { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden = Coq_xH }))
  in
  let k_UU03b4_ =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden = Coq_xH }
        (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let k2 =
    coq_Qinv
      (coq_Qmult
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden =
          Coq_xH }
          (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        (coq_Qplus
          (coq_Qplus
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
              Coq_xH } s)
            mc)
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let k2p =
    coq_Qinv
      (coq_Qmult
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))));
          coq_Qden = Coq_xH }
          (coq_Qplus k1e { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        (coq_Qplus
          (coq_Qplus
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
              Coq_xH } s)
            mc)
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let hk_UU03b4_T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden =
          Coq_xH }
          (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let hk2T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))));
            coq_Qden = Coq_xH }
            (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
          (coq_Qplus
            (coq_Qplus
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                Coq_xH } s)
              mc)
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let hk2pT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            Coq_xH))))))))))); coq_Qden = Coq_xH }
            (coq_Qplus k1e { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
          (coq_Qplus
            (coq_Qplus
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                Coq_xH } s)
              mc)
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let h12T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let h14T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let s0 = b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2T hk2pT in
  let Coq_existT (x0, a) = s0 in
  let Coq_pair (r0, s1) = a in
  let hc12r =
    b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
      Coq_xH) } h12T
  in
  let hepsk_UU03b4_ =
    real_mult_positive eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let hqtr =
    real_mult_positive
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) } h14T)
      (real_inv_pos_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
  in
  let delta =
    real_min
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
  in
  let hdpos =
    real_min_pos
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_min_pos
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_))
        (real_min_pos x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) })
          r0 hc12r)
        hepsk_UU03b4_)
      hqtr
  in
  Coq_existT (delta, (Coq_pair (hdpos, (fun h hh hxh eps' heps' ->
  let s2 = b5dM_b5c_d_proj_le_one x in
  let Coq_existT (x1, _) = s2 in
  let s3 = b5dM_b5n_eps_proj_lt eps heps in
  let Coq_existT (_, a0) = s3 in
  let Coq_pair (_, s4) = a0 in
  let Coq_existT (x2, _) = s4 in
  let s5 = b5dM_b5n_eps_proj_lt eps' heps' in
  let Coq_existT (x3, a1) = s5 in
  let Coq_pair (_, s6) = a1 in
  let Coq_existT (x4, _) = s6 in
  let eta =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) } x3
  in
  let hetaT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } x3)
  in
  let hhA =
    real_min_lt_l h
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhE =
    real_min_lt_r h
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhAA =
    real_min_lt_l h
      (real_min x0
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhlr =
    real_min_lt_r h
      (real_min x0
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhda =
    real_min_lt_l h x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      hhAA
  in
  let hh12 =
    real_min_lt_r h x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      hhAA
  in
  let hhq_r =
    real_lt_le_trans (real_abs h)
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hhE
      (RealSetoid.real_eq_le
        (real_mult
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (real_mult
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (b5dI_inv_leaf_witness_eq eps k2 heps hk2T))
  in
  let s7 = b5n_h_pts h eps k_UU03b4_ k2 heps hk_UU03b4_T hk2T hhlr hh12 hhq_r
  in
  let Coq_existT (x5, _) = s7 in
  let s8 = s1 h hhda hxh eps' heps' in
  let Coq_existT (x6, _) = s8 in
  let s9 = b5i_rs_addcol x hx h hxh eta hetaT in
  let Coq_existT (x7, _) = s9 in
  let nmax =
    PeanoNat.Nat.max (PeanoNat.Nat.max x2 x4)
      (PeanoNat.Nat.max (PeanoNat.Nat.max x5 x6) (PeanoNat.Nat.max x7 x1))
  in
  Coq_inl (Coq_existT (eta, (Coq_pair (hetaT, (Coq_existT (nmax, (fun n _ ->
  coq_Qlt_to_QltT eta
    (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1 (real_abs (b5a_comp_err_sin x hx h hxh)) n)))))))))))))

(** val b5dI_cos_atan_diff_closed_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
    coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
    (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real ->
    real_lt -> real_le) coq_And) sigT **)

let b5dI_cos_atan_diff_closed_r_exp r x hxr ms mc c4 _ _ eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let s = coq_Qplus ms mc in
  let k1e =
    coq_Qplus
      (coq_Qmult mc
        (coq_Qplus
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
            Coq_xH } c4)
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (coq_Qmult ms
        (coq_Qplus
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
            Coq_xH } c4)
          { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden = Coq_xH }))
  in
  let k_UU03b4_ =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden = Coq_xH }
        (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let k2 =
    coq_Qinv
      (coq_Qmult
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden =
          Coq_xH }
          (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        (coq_Qplus
          (coq_Qplus
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
              Coq_xH } s)
            ms)
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let k2p =
    coq_Qinv
      (coq_Qmult
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))));
          coq_Qden = Coq_xH }
          (coq_Qplus k1e { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        (coq_Qplus
          (coq_Qplus
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
              Coq_xH } s)
            ms)
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let hk_UU03b4_T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden =
          Coq_xH }
          (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let hk2T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))));
            coq_Qden = Coq_xH }
            (coq_Qplus s { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
          (coq_Qplus
            (coq_Qplus
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                Coq_xH } s)
              ms)
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let hk2pT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            Coq_xH))))))))))); coq_Qden = Coq_xH }
            (coq_Qplus k1e { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
          (coq_Qplus
            (coq_Qplus
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                Coq_xH } s)
              ms)
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let h12T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let h14T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let s0 = b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2T hk2pT in
  let Coq_existT (x0, a) = s0 in
  let Coq_pair (r0, s1) = a in
  let hc12r =
    b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
      Coq_xH) } h12T
  in
  let hepsk_UU03b4_ =
    real_mult_positive eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let hqtr =
    real_mult_positive
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) } h14T)
      (real_inv_pos_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
  in
  let delta =
    real_min
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
  in
  let hdpos =
    real_min_pos
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_min_pos
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_))
        (real_min_pos x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) })
          r0 hc12r)
        hepsk_UU03b4_)
      hqtr
  in
  Coq_existT (delta, (Coq_pair (hdpos, (fun h hh hxh eps' heps' ->
  let s2 = b5dM_b5c_d_proj_le_one x in
  let Coq_existT (x1, _) = s2 in
  let s3 = b5dM_b5n_eps_proj_lt eps heps in
  let Coq_existT (_, a0) = s3 in
  let Coq_pair (_, s4) = a0 in
  let Coq_existT (x2, _) = s4 in
  let s5 = b5dM_b5n_eps_proj_lt eps' heps' in
  let Coq_existT (x3, a1) = s5 in
  let Coq_pair (_, s6) = a1 in
  let Coq_existT (x4, _) = s6 in
  let eta =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) } x3
  in
  let hetaT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } x3)
  in
  let hhA =
    real_min_lt_l h
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhE =
    real_min_lt_r h
      (real_min
        (real_min x0
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            Coq_xH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhAA =
    real_min_lt_l h
      (real_min x0
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhlr =
    real_min_lt_r h
      (real_min x0
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhda =
    real_min_lt_l h x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      hhAA
  in
  let hh12 =
    real_min_lt_r h x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      hhAA
  in
  let hhq_r =
    real_lt_le_trans (real_abs h)
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_mult
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hhE
      (RealSetoid.real_eq_le
        (real_mult
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (real_mult
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (b5dI_inv_leaf_witness_eq eps k2 heps hk2T))
  in
  let s7 = b5n_h_pts h eps k_UU03b4_ k2 heps hk_UU03b4_T hk2T hhlr hh12 hhq_r
  in
  let Coq_existT (x5, _) = s7 in
  let s8 = s1 h hhda hxh eps' heps' in
  let Coq_existT (x6, _) = s8 in
  let s9 = b5d_rs_addcol_cos x hx h hxh eta hetaT in
  let Coq_existT (x7, _) = s9 in
  let nmax =
    PeanoNat.Nat.max (PeanoNat.Nat.max x2 x4)
      (PeanoNat.Nat.max (PeanoNat.Nat.max x5 x6) (PeanoNat.Nat.max x7 x1))
  in
  Coq_inl (Coq_existT (eta, (Coq_pair (hetaT, (Coq_existT (nmax, (fun n _ ->
  coq_Qlt_to_QltT eta
    (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1 (real_abs (b5a_comp_err_cos x hx h hxh)) n)))))))))))))

(** val b5dI_E_diff_closed_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> coq_Q -> coq_Q ->
    coq_QleT' -> (nat -> coq_QleT') -> coq_Real -> real_lt -> (coq_Real,
    (real_lt, coq_Real -> real_lt -> (nat -> coq_QleT') -> coq_Real ->
    real_lt -> real_le) coq_And) sigT **)

let b5dI_E_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4 eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let k_UU03b4_ =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden = Coq_xH }
        (coq_Qplus msr { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let hk_UU03b4_T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))); coq_Qden =
          Coq_xH }
          (coq_Qplus msr { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let hkT4 =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let hkT8 =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO Coq_xH))) }
  in
  let hkT16 =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let hepsS =
    b5dI_real_mult_positive_exp eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      heps
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) } hkT4)
  in
  let hepsC =
    b5dI_real_mult_positive_exp eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      heps
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) } hkT4)
  in
  let s =
    b5dI_sin_atan_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4
      (real_mult eps
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) }))
      hepsS
  in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  let s0 =
    b5dI_cos_atan_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4
      (real_mult eps
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) }))
      hepsC
  in
  let Coq_existT (x1, a0) = s0 in
  let Coq_pair (r2, r3) = a0 in
  let hepsk_UU03b4_ =
    b5dI_real_mult_positive_exp eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let delta = real_min (real_min x0 x1) (real_mult eps (real_const k_UU03b4_))
  in
  let hdpos =
    real_min_pos (real_min x0 x1) (real_mult eps (real_const k_UU03b4_))
      (real_min_pos x0 x1 r0 r2) hepsk_UU03b4_
  in
  Coq_existT (delta, (Coq_pair (hdpos, (fun h hh hxh eps' heps' ->
  let s1 = b5dM_b5c_d_proj_le_one x in
  let Coq_existT (x2, _) = s1 in
  let s2 = b5dM_b5n_eps_proj_lt eps heps in
  let Coq_existT (_, a1) = s2 in
  let Coq_pair (_, s3) = a1 in
  let Coq_existT (x3, _) = s3 in
  let s4 = b5dM_b5n_eps_proj_lt eps' heps' in
  let Coq_existT (x4, a2) = s4 in
  let Coq_pair (_, s5) = a2 in
  let Coq_existT (x5, _) = s5 in
  let eta =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) } x4
  in
  let hetaT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } x4)
  in
  let hhA =
    real_min_lt_l h (real_min x0 x1) (real_mult eps (real_const k_UU03b4_)) hh
  in
  let hhlr =
    real_min_lt_r h (real_min x0 x1) (real_mult eps (real_const k_UU03b4_)) hh
  in
  let hh_UU03b4_S = real_min_lt_l h x0 x1 hhA in
  let hh_UU03b4_C = real_min_lt_r h x0 x1 hhA in
  let hepsS'' =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) })
      heps'
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xO Coq_xH))) } hkT8)
  in
  let hshS =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
      heps'
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) } hkT16)
  in
  let s6 =
    b5i_abs_le_pointwise (b5a_comp_err_sin x hx h hxh)
      (real_plus
        (real_mult
          (real_mult eps
            (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
              (Coq_xO Coq_xH)) }))
          (real_abs h))
        (real_mult eps'
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            (Coq_xO Coq_xH))) })))
      (r1 h hh_UU03b4_S hxh
        (real_mult eps'
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            (Coq_xO Coq_xH))) }))
        hepsS'')
      (real_mult eps'
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO Coq_xH)))) }))
      hshS
  in
  let Coq_existT (x6, _) = s6 in
  let hepsC'' =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) })
      heps'
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xO Coq_xH))) } hkT8)
  in
  let hshC =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
      heps'
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) } hkT16)
  in
  let s7 =
    b5i_abs_le_pointwise (b5a_comp_err_cos x hx h hxh)
      (real_plus
        (real_mult
          (real_mult eps
            (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
              (Coq_xO Coq_xH)) }))
          (real_abs h))
        (real_mult eps'
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            (Coq_xO Coq_xH))) })))
      (r3 h hh_UU03b4_C hxh
        (real_mult eps'
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            (Coq_xO Coq_xH))) }))
        hepsC'')
      (real_mult eps'
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO Coq_xH)))) }))
      hshC
  in
  let Coq_existT (x7, _) = s7 in
  let s8 = b5i_h_le_enk h eps k_UU03b4_ hhlr hk_UU03b4_T in
  let Coq_existT (x8, _) = s8 in
  let s9 = b5e_E_dec_proj x hx h hxh in
  let Coq_existT (x9, _) = s9 in
  let nmax =
    PeanoNat.Nat.max (PeanoNat.Nat.max x3 x5)
      (PeanoNat.Nat.max (PeanoNat.Nat.max x9 x8)
        (PeanoNat.Nat.max (PeanoNat.Nat.max x6 x7) x2))
  in
  Coq_inl (Coq_existT (eta, (Coq_pair (hetaT, (Coq_existT (nmax, (fun n _ ->
  coq_Qlt_to_QltT eta
    (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1
        (real_abs
          (real_plus (b5a_E (real_plus x h) hxh)
            (real_opp
              (real_plus (b5a_E x hx)
                (real_mult (real_mult x (b5a_E x hx))
                  (real_mult (b5a_atan_d x) h))))))
        n)))))))))))))

(** val b5dJ_two_pos_exp : real_lt **)

let b5dJ_two_pos_exp =
  Coq_existT ({ coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) },
    (Coq_pair (Coq_id_refl, (Coq_existT (O, (fun _ _ -> Coq_id_refl))))))

(** val b5dJ_log_diff_dx_exp :
    coq_Real -> real_lt -> coq_Real -> real_lt -> (coq_Real, (real_lt,
    coq_Real -> real_lt -> real_lt -> coq_Real -> real_lt -> real_le)
    coq_And) sigT **)

let b5dJ_log_diff_dx_exp x0 hx0 eps heps =
  let two_inv = real_inv_pos (real_plus real_one real_one) real_two_pos_local
  in
  let four_inv = real_mult two_inv two_inv in
  let eight_inv = real_mult four_inv two_inv in
  let half_x = real_mult two_inv x0 in
  let eps_x2 = real_mult eps (real_mult x0 x0) in
  let eps4 = real_mult four_inv eps_x2 in
  let two_invJ = real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp
  in
  let four_invJ = real_mult two_invJ two_invJ in
  let half_xJ = real_mult two_invJ x0 in
  let eps4J = real_mult four_invJ eps_x2 in
  let delta = real_min half_xJ eps4J in
  Coq_existT (delta, (Coq_pair
  ((real_min_pos
     (real_mult (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
       x0)
     (real_mult
       (real_mult
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult eps (real_mult x0 x0)))
     (real_mult_positive
       (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) x0
       (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp) hx0)
     (real_mult_positive
       (real_mult
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult eps (real_mult x0 x0))
       (real_mult_positive
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult_positive eps (real_mult x0 x0) heps
         (real_mult_positive x0 x0 hx0 hx0)))),
  (fun h hh hxh eps' heps' ->
  let share = real_mult eight_inv eps' in
  let hshare =
    real_mult_positive eight_inv eps'
      (real_mult_positive
        (real_mult
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_mult_positive
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
        (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
      heps'
  in
  let t = real_mult h (real_inv_pos x0 hx0) in
  let htwo_eq = fun eps0 heps0 ->
    let s = real_inv_proj (real_plus real_one real_one) real_two_pos_local in
    let Coq_existT (x, _) = s in
    Coq_existT (x, (fun n _ ->
    qltT_eq_compat_l { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qabs
        (coq_Qminus
          (projT1
            (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n)
          (projT1
            (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n)))
      eps0 heps0))
  in
  let hfour_eq =
    RealSetoid.real_eq_mult_compat two_invJ two_invJ two_inv two_inv htwo_eq
      htwo_eq
  in
  let hhalf_le =
    RealSetoid.real_eq_le (real_mult two_invJ x0) (real_mult two_inv x0)
      (RealSetoid.real_eq_mult_compat two_invJ x0 two_inv x0 htwo_eq
        (real_eq_refl x0))
  in
  let heps4_le =
    RealSetoid.real_eq_le (real_mult four_invJ eps_x2)
      (real_mult four_inv eps_x2)
      (RealSetoid.real_eq_mult_compat four_invJ eps_x2 four_inv eps_x2
        hfour_eq (real_eq_refl eps_x2))
  in
  let hh_halfJ = real_min_lt_l h half_xJ eps4J hh in
  let hh_half = real_lt_le_trans (real_abs h) half_xJ half_x hh_halfJ hhalf_le
  in
  let ht_half = real_t_abs_lt_half x0 h hx0 hh_half in
  let ht_lower = real_abs_lt_lower t two_inv ht_half in
  let hhalf_t = real_half_lt_one_plus_t t ht_lower in
  let htpos =
    real_lt_trans real_zero two_inv (real_plus real_one t)
      (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local)
      hhalf_t
  in
  let hh_eps4J = real_min_lt_r h half_xJ eps4J hh in
  let hh_eps4 = real_lt_le_trans (real_abs h) eps4J eps4 hh_eps4J heps4_le in
  let x = real_plus (real_log (real_plus real_one t) htpos) (real_opp t) in
  let hDX =
    real_eq_trans
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h))))
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_plus (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h))))
      x
      (RealSetoid.real_eq_plus_compat (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))
        (real_log (real_plus x0 h) hxh)
        (real_plus (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        (real_eq_refl (real_log (real_plus x0 h) hxh))
        (real_opp_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))
      (real_eq_trans
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_plus (real_opp (real_log x0 hx0))
            (real_opp (real_mult (real_inv_pos x0 hx0) h))))
        (real_plus
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp (real_log x0 hx0)))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        x
        (real_plus_assoc (real_log (real_plus x0 h) hxh)
          (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        (RealSetoid.real_eq_plus_compat
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp (real_log x0 hx0)))
          (real_opp (real_mult (real_inv_pos x0 hx0) h))
          (real_log (real_plus real_one t) htpos) (real_opp t)
          (real_log_plus_diff x0 h hx0 hxh htpos)
          (real_eq_trans (real_opp (real_mult (real_inv_pos x0 hx0) h))
            (real_opp (real_mult h (real_inv_pos x0 hx0))) (real_opp t)
            (RealSetoid.real_eq_opp_compat
              (real_mult (real_inv_pos x0 hx0) h)
              (real_mult h (real_inv_pos x0 hx0))
              (real_mult_comm (real_inv_pos x0 hx0) h))
            (real_eq_refl (real_opp t)))))
  in
  let hXup =
    real_le_trans x (real_plus (real_plus t share) (real_opp t)) share
      (real_le_plus_compat (real_log (real_plus real_one t) htpos)
        (real_plus t share) (real_opp t) (real_opp t)
        (real_log_one_plus_le_eps t share htpos hshare)
        (real_le_refl (real_opp t)))
      (RealSetoid.real_eq_le (real_plus (real_plus t share) (real_opp t))
        share
        (real_eq_trans (real_plus (real_plus t share) (real_opp t))
          (real_plus t (real_plus share (real_opp t))) share
          (real_eq_sym (real_plus t (real_plus share (real_opp t)))
            (real_plus (real_plus t share) (real_opp t))
            (real_plus_assoc t share (real_opp t)))
          (real_eq_trans (real_plus t (real_plus share (real_opp t)))
            (real_plus (real_plus t (real_opp t)) share) share
            (real_eq_trans (real_plus t (real_plus share (real_opp t)))
              (real_plus t (real_plus (real_opp t) share))
              (real_plus (real_plus t (real_opp t)) share)
              (RealSetoid.real_eq_plus_compat t
                (real_plus share (real_opp t)) t
                (real_plus (real_opp t) share) (real_eq_refl t)
                (real_plus_comm share (real_opp t)))
              (real_plus_assoc t (real_opp t) share))
            (real_eq_trans (real_plus (real_plus t (real_opp t)) share)
              (real_plus real_zero share) share
              (RealSetoid.real_eq_plus_compat (real_plus t (real_opp t))
                share real_zero share (real_plus_opp t) (real_eq_refl share))
              (real_eq_trans (real_plus real_zero share)
                (real_plus share real_zero) share
                (real_plus_comm real_zero share) (real_plus_zero share))))))
  in
  let hXdown =
    real_le_trans (real_opp x)
      (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus share share))
      (RealSetoid.real_eq_le
        (real_opp
          (real_plus (real_log (real_plus real_one t) htpos) (real_opp t)))
        (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
        (real_eq_trans
          (real_opp
            (real_plus (real_log (real_plus real_one t) htpos) (real_opp t)))
          (real_plus (real_opp (real_log (real_plus real_one t) htpos))
            (real_opp (real_opp t)))
          (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
          (real_opp_plus (real_log (real_plus real_one t) htpos) (real_opp t))
          (real_eq_trans
            (real_plus (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp (real_opp t)))
            (real_plus (real_opp (real_opp t))
              (real_opp (real_log (real_plus real_one t) htpos)))
            (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
            (real_plus_comm
              (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp (real_opp t)))
            (RealSetoid.real_eq_plus_compat (real_opp (real_opp t))
              (real_opp (real_log (real_plus real_one t) htpos)) t
              (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp_opp t)
              (real_eq_refl
                (real_opp (real_log (real_plus real_one t) htpos)))))))
      (real_le_trans
        (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
        (real_plus
          (real_mult (real_mult t t)
            (real_inv_pos (real_plus real_one t) htpos))
          share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share share))
        (real_t_minus_log_bound t share htpos hshare)
        (real_le_trans
          (real_plus
            (real_mult (real_mult t t)
              (real_inv_pos (real_plus real_one t) htpos))
            share)
          (real_plus
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one)) share)
            share)
          (real_plus
            (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share share))
          (real_le_plus_compat
            (real_mult (real_mult t t)
              (real_inv_pos (real_plus real_one t) htpos))
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one)) share)
            share share
            (real_quad_div_le_two_eps t (real_plus real_one t) share htpos
              hhalf_t hshare)
            (real_le_refl share))
          (RealSetoid.real_eq_le
            (real_plus
              (real_plus
                (real_mult (real_mult t t) (real_plus real_one real_one))
                share)
              share)
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one))
              (real_plus share share))
            (real_eq_sym
              (real_plus
                (real_mult (real_mult t t) (real_plus real_one real_one))
                (real_plus share share))
              (real_plus
                (real_plus
                  (real_mult (real_mult t t) (real_plus real_one real_one))
                  share)
                share)
              (real_plus_assoc
                (real_mult (real_mult t t) (real_plus real_one real_one))
                share share)))))
  in
  let habs =
    real_abs_le_quad_eps x t share (real_plus share share) share hXup hXdown
      hshare (real_plus_positive share share hshare hshare) hshare
  in
  let hquad = real_quad_t_le_h_eps x0 h eps share hx0 hh_eps4 heps hshare in
  let habsD =
    real_le_trans
      (real_abs
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_opp
            (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
      (real_abs x)
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (RealSetoid.real_eq_le
        (real_abs
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp
              (real_plus (real_log x0 hx0)
                (real_mult (real_inv_pos x0 hx0) h)))))
        (real_abs x)
        (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp
              (real_plus (real_log x0 hx0)
                (real_mult (real_inv_pos x0 hx0) h))))
          x hDX))
      habs
  in
  let hmid =
    real_le_trans
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus (real_plus share (real_plus share share)) share))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
        (real_plus share
          (real_plus (real_plus share (real_plus share share)) share)))
      (RealSetoid.real_eq_le
        (real_plus
          (real_plus
            (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share (real_plus share share)))
          share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_plus share (real_plus share share)) share))
        (real_eq_sym
          (real_plus
            (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus (real_plus share (real_plus share share)) share))
          (real_plus
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one))
              (real_plus share (real_plus share share)))
            share)
          (real_plus_assoc
            (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share (real_plus share share)) share)))
      (real_le_trans
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_plus share (real_plus share share)) share))
        (real_plus
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
          (real_plus (real_plus share (real_plus share share)) share))
        (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
          (real_plus share
            (real_plus (real_plus share (real_plus share share)) share)))
        (real_le_plus_compat
          (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
          (real_plus (real_plus share (real_plus share share)) share)
          (real_plus (real_plus share (real_plus share share)) share) hquad
          (real_le_refl
            (real_plus (real_plus share (real_plus share share)) share)))
        (RealSetoid.real_eq_le
          (real_plus
            (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
            (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
            (real_plus share
              (real_plus (real_plus share (real_plus share share)) share)))
          (real_eq_sym
            (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
              (real_plus share
                (real_plus (real_plus share (real_plus share share)) share)))
            (real_plus
              (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                share)
              (real_plus (real_plus share (real_plus share share)) share))
            (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
              share
              (real_plus (real_plus share (real_plus share share)) share)))))
  in
  let hfinal =
    let Coq_existT (x1, a) = real_two_pos_local in
    let Coq_pair (q, s) = a in
    let Coq_existT (x2, q0) = s in
    let two_inv0 =
      real_inv_pos (real_plus real_one real_one) (Coq_existT (x1, (Coq_pair
        (q, (Coq_existT (x2, q0))))))
    in
    let four_inv0 = real_mult two_inv0 two_inv0 in
    let eight_inv0 = real_mult four_inv0 two_inv0 in
    let share0 = real_mult eight_inv0 eps' in
    let Coq_existT (_, a0) = heps in
    let Coq_pair (_, s0) = a0 in
    let Coq_existT (x3, _) = s0 in
    let Coq_existT (x4, a1) = heps' in
    let Coq_pair (_, s1) = a1 in
    let Coq_existT (x5, _) = s1 in
    let eps0q =
      coq_Qmult { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xO Coq_xH))) } x4
    in
    let heps0q = coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } eps0q in
    RealSetoid.real_lt_le_iff_req
      (real_plus (real_mult (real_mult two_inv0 eps) (real_abs h))
        (real_plus share0
          (real_plus (real_plus share0 (real_plus share0 share0)) share0)))
      (real_plus (real_mult eps (real_abs h)) eps') (Coq_inl (Coq_existT
      (eps0q, (Coq_pair (heps0q, (Coq_existT
      ((PeanoNat.Nat.max x5 (PeanoNat.Nat.max x2 x3)), (fun n _ ->
      coq_Qlt_to_QltT eps0q
        (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
          (projT1
            (real_plus (real_mult (real_mult two_inv0 eps) (real_abs h))
              (real_plus share0
                (real_plus (real_plus share0 (real_plus share0 share0))
                  share0)))
            n))))))))))
  in
  real_le_trans
    (real_abs
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
    (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
      (real_plus share
        (real_plus (real_plus share (real_plus share share)) share)))
    (real_plus (real_mult eps (real_abs h)) eps')
    (real_le_trans
      (real_abs
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_opp
            (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
        (real_plus share
          (real_plus (real_plus share (real_plus share share)) share)))
      habsD hmid)
    hfinal))))

(** val b5dJ_LogErr_delta_exp :
    coq_Real -> coq_Real -> real_lt -> (coq_Real, (real_lt, coq_Real ->
    coq_Real -> real_lt -> real_lt -> real_le) coq_And) sigT **)

let b5dJ_LogErr_delta_exp x epsL hepsL =
  let s = b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x) epsL hepsL in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r, r0) = a in
  Coq_existT (x0, (Coq_pair (r, (fun h epsL' hepsL' hh_UU0394_ ->
  let logexpr =
    real_plus
      (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
      (real_opp
        (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
          (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
            (b5f_Du x h))))
  in
  let hraw = r0 (b5f_Du x h) hh_UU0394_ (b5f_u_plus_Du_pos x h) epsL' hepsL'
  in
  let heq =
    real_eq_trans
      (real_plus
        (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h)))))
      (real_plus
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h)))))
      (real_plus
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (b5a_atan_d x) (b5f_Du x h)))))
      (RealSetoid.real_eq_plus_compat
        (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h))))
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h))))
        (real_log_wd (real_plus (b5f_u x) (b5f_Du x h))
          (b5f_u (real_plus x h)) (b5f_u_plus_Du_pos x h)
          (b5a_one_plus_sq_pos (real_plus x h)) (b5f_u_Du_eq x h))
        (real_eq_refl
          (real_opp
            (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                (b5f_Du x h))))))
      (real_eq_refl
        (real_plus
          (real_log
            (real_plus real_one (real_mult (real_plus x h) (real_plus x h)))
            (b5a_one_plus_sq_pos (real_plus x h)))
          (real_opp
            (real_plus
              (real_log (real_plus real_one (real_mult x x))
                (b5a_one_plus_sq_pos x))
              (real_mult
                (real_inv_pos (real_plus real_one (real_mult x x))
                  (b5a_one_plus_sq_pos x))
                (b5f_Du x h))))))
  in
  real_le_trans (real_abs (b5f_LogErr x h)) (real_abs logexpr)
    (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')
    (RealSetoid.real_eq_le (real_abs (b5f_LogErr x h)) (real_abs logexpr)
      (real_abs_eq_compat (b5f_LogErr x h) logexpr
        (real_eq_sym logexpr (b5f_LogErr x h) heq)))
    hraw))))

(** val b5d3_exp_arch4_C : coq_Q **)

let b5d3_exp_arch4_C =
  coq_Qplus
    (exp_series (S (S (S (S (S (S (S (S (S (S (S O))))))))))) { coq_Qnum =
      (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden = Coq_xH })
    (coq_Qmult
      (coq_Qdiv
        (q_pow { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
          Coq_xH } (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
        (q_fact (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))
      (coq_Qplus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
        (Zpos Coq_xH); coq_Qden = Coq_xH }))

(** val b5d3_exp_arch4_C_ge1 : coq_QleT' **)

let b5d3_exp_arch4_C_ge1 =
  coq_Qle_to_QleT' { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
    b5d3_exp_arch4_C

(** val b5d3_exp_arch4_C_all : nat -> coq_QleT' **)

let b5d3_exp_arch4_C_all j =
  coq_Qle_to_QleT'
    (exp_series j { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
      Coq_xH })
    b5d3_exp_arch4_C

(** val b5dK_real_mult_positive_exp :
    coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt **)

let b5dK_real_mult_positive_exp a b ha hb =
  let Coq_existT (x, a0) = ha in
  let Coq_pair (_, s) = a0 in
  let Coq_existT (x0, _) = s in
  let Coq_existT (x1, a1) = hb in
  let Coq_pair (_, s0) = a1 in
  let Coq_existT (x2, _) = s0 in
  Coq_existT ((coq_Qmult x x1), (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } (coq_Qmult x x1)),
  (Coq_existT ((PeanoNat.Nat.max x0 x2), (fun n _ ->
  coq_Qlt_to_QltT (coq_Qmult x x1)
    (coq_Qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val b5dK_real_abs_plus_one_pos_exp : coq_Real -> real_lt **)

let b5dK_real_abs_plus_one_pos_exp a =
  Coq_existT
    ((coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
       (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }),
    (Coq_pair
    ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
       (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
         (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })),
    (Coq_existT (O, (fun n _ ->
    coq_Qlt_to_QltT
      (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
        (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (coq_Qminus (projT1 (real_plus real_one (real_abs a)) n)
        (projT1 real_zero n))))))))

(** val b5dK_real_abs_scaling_le_exp :
    coq_Real -> coq_Real -> coq_Real -> coq_Real -> real_lt -> real_lt ->
    real_le **)

let b5dK_real_abs_scaling_le_exp a eps eps' h heps heps' =
  Coq_inl
    (let Coq_existT (_, a0) = heps in
     let Coq_pair (_, s) = a0 in
     let Coq_existT (x, _) = s in
     let Coq_existT (x0, a1) = heps' in
     let Coq_pair (_, s0) = a1 in
     let Coq_existT (x1, _) = s0 in
     let s1 = real_norm_bounded a in
     let Coq_existT (x2, _) = s1 in
     let s2 =
       real_inv_proj (real_plus real_one (real_abs a))
         (b5dK_real_abs_plus_one_pos_exp a)
     in
     let Coq_existT (x3, _) = s2 in
     let m2 =
       coq_Qplus x2 { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }
     in
     Coq_existT ((coq_Qmult x0 (coq_Qinv m2)), (Coq_pair
     ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
        (coq_Qmult x0 (coq_Qinv m2))),
     (Coq_existT ((PeanoNat.Nat.max (PeanoNat.Nat.max x x1) x3), (fun n _ ->
     coq_Qlt_to_QltT (coq_Qmult x0 (coq_Qinv m2))
       (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
         (projT1
           (real_mult (real_abs a)
             (real_plus
               (real_mult
                 (real_mult eps
                   (real_inv_pos (real_plus real_one (real_abs a))
                     (b5dK_real_abs_plus_one_pos_exp a)))
                 (real_abs h))
               (real_mult eps'
                 (real_inv_pos (real_plus real_one (real_abs a))
                   (b5dK_real_abs_plus_one_pos_exp a)))))
           n)))))))))

(** val b5dK_exp_minus_one_linear_closed_exp :
    coq_Real -> real_lt -> (coq_Real, (real_eq, (real_lt, coq_Real -> real_lt
    -> coq_Real -> real_lt -> real_le) coq_And) coq_And) sigT **)

let b5dK_exp_minus_one_linear_closed_exp eps heps =
  let delta =
    real_min
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      (real_mult eps
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) }))
  in
  Coq_existT (delta, (Coq_pair
  ((real_eq_refl
     (real_min
       (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
       (real_mult eps
         (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
           Coq_xH)) })))),
  (Coq_pair
  ((real_min_pos
     (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
     (real_mult eps
       (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
         Coq_xH)) }))
     (real_const_pos_f1 { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
       Coq_xH) })
     (b5dK_real_mult_positive_exp eps
       (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
         Coq_xH)) })
       heps
       (real_const_pos_f1 { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
         (Coq_xO Coq_xH)) }))),
  (fun h hh eps' heps' ->
  let hh_half =
    real_min_lt_l h
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      (real_mult eps
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) }))
      hh
  in
  let hh_eps4 =
    real_min_lt_r h
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      (real_mult eps
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) }))
      hh
  in
  Coq_inl
  (let Coq_existT (_, a) = heps in
   let Coq_pair (_, s) = a in
   let Coq_existT (x, _) = s in
   let Coq_existT (x0, a0) = heps' in
   let Coq_pair (q, s0) = a0 in
   let Coq_existT (x1, _) = s0 in
   let Coq_existT (_, a1) = hh_half in
   let Coq_pair (_, s1) = a1 in
   let Coq_existT (x2, _) = s1 in
   let Coq_existT (_, a2) = hh_eps4 in
   let Coq_pair (_, s2) = a2 in
   let Coq_existT (x3, _) = s2 in
   Coq_existT (x0, (Coq_pair (q, (Coq_existT
   ((PeanoNat.Nat.max
      (PeanoNat.Nat.max (PeanoNat.Nat.max x x1) (PeanoNat.Nat.max x2 x3)) (S
      (S O))),
   (fun n _ ->
   coq_Qlt_to_QltT x0
     (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1
         (real_abs
           (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one))
             (real_opp h)))
         n)))))))))))))))

(** val b5dK_gdiff_pts_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt -> coq_Q
    -> coq_Q -> coq_QltT -> coq_QltT -> (coq_Real, (real_lt, coq_Real ->
    real_lt -> coq_Real -> real_lt -> (nat, __) sigT) coq_And) sigT **)

let b5dK_gdiff_pts_r_exp r x hxr eps heps k2 k2p _ hk2p =
  let kL =
    coq_Qmult k2 { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let hkLT = coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } kL in
  let epsL = real_mult eps (real_const kL) in
  let hepsL =
    b5dK_real_mult_positive_exp eps (real_const kL) heps
      (b5dM_real_const_pos kL hkLT)
  in
  let s = b5dJ_LogErr_delta_exp x epsL hepsL in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  let a0 =
    real_mult x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xI Coq_xH))) })
  in
  let b = real_mult eps (real_const kL) in
  let c = real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let _UU03b4_g = real_min (real_min a0 b) c in
  let h12T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let h112T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xI Coq_xH))) }
  in
  let hA0 =
    b5dK_real_mult_positive_exp x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xI Coq_xH))) })
      r0
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xI Coq_xH))) } h112T)
  in
  let hB0 =
    b5dK_real_mult_positive_exp eps (real_const kL) heps
      (b5dM_real_const_pos kL hkLT)
  in
  let hC0 =
    b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
      Coq_xH) } h12T
  in
  let h_UU03b4_g0 =
    real_min_pos (real_min a0 b) c (real_min_pos a0 b hA0 hB0) hC0
  in
  Coq_existT (_UU03b4_g, (Coq_pair (h_UU03b4_g0,
  (fun h hh_UU03b4_ eps' heps' ->
  let hhAB = real_min_lt_l h (real_min a0 b) c hh_UU03b4_ in
  let hhA = real_min_lt_l h a0 b hhAB in
  let hhB = real_min_lt_r h a0 b hhAB in
  let hhC = real_min_lt_r h (real_min a0 b) c hh_UU03b4_ in
  let hact = b5f_Du_act_delta r x hxr h x0 r0 hhA hhC in
  let epsL'' = real_mult eps' (real_const k2p) in
  let hepsL'' =
    b5dK_real_mult_positive_exp eps' (real_const k2p) heps'
      (b5dM_real_const_pos k2p hk2p)
  in
  let hlog = r1 h epsL'' hepsL'' hact in
  let s0 =
    b5i_abs_le_pointwise (b5f_LogErr x h)
      (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'') hlog epsL''
      hepsL''
  in
  let Coq_existT (x1, _) = s0 in
  let Coq_existT (_, a1) = heps in
  let Coq_pair (_, s1) = a1 in
  let Coq_existT (x2, _) = s1 in
  let Coq_existT (_, a2) = heps' in
  let Coq_pair (_, s2) = a2 in
  let Coq_existT (x3, _) = s2 in
  let Coq_existT (_, a3) = hhB in
  let Coq_pair (_, s3) = a3 in
  let Coq_existT (x4, _) = s3 in
  let Coq_existT (_, a4) = hhC in
  let Coq_pair (_, s4) = a4 in
  let Coq_existT (x5, _) = s4 in
  let s5 = b5dM_b5c_d_proj_le_one x in
  let Coq_existT (x6, _) = s5 in
  let n =
    PeanoNat.Nat.max x1
      (PeanoNat.Nat.max x6
        (PeanoNat.Nat.max x2 (PeanoNat.Nat.max x3 (PeanoNat.Nat.max x4 x5))))
  in
  Coq_existT (n, __)))))

(** val b5dK_exp_part_bound_closed_r_exp :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Real -> real_lt ->
    (coq_Real, (real_lt, coq_Real -> real_lt -> coq_Real -> real_lt ->
    real_le) coq_And) sigT **)

let b5dK_exp_part_bound_closed_r_exp r x hxr eps heps =
  let sx = b5a_S x in
  let invM =
    real_inv_pos (real_plus real_one (real_abs sx))
      (b5dK_real_abs_plus_one_pos_exp sx)
  in
  let eps0 =
    real_mult (real_mult eps (real_const (coq_Qinv (b5j_Kvq r)))) invM
  in
  let hKqinvT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qinv (b5j_Kvq r))
  in
  let hinvM0 =
    real_inv_pos_pos (real_plus real_one (real_abs sx))
      (b5dK_real_abs_plus_one_pos_exp sx)
  in
  let heps0 =
    b5dK_real_mult_positive_exp
      (real_mult eps (real_const (coq_Qinv (b5j_Kvq r)))) invM
      (b5dK_real_mult_positive_exp eps (real_const (coq_Qinv (b5j_Kvq r)))
        heps (b5dM_real_const_pos (coq_Qinv (b5j_Kvq r)) hKqinvT))
      hinvM0
  in
  let heps0le = RealSetoid.real_lt_le_iff_req real_zero eps0 (Coq_inl heps0)
  in
  let hkLpos = b5dM_real_const_pos b5j_kL b5j_kL_posT in
  let s = b5dJ_LogErr_delta_exp x (real_const b5j_kL) hkLpos in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  let s0 = b5dK_exp_minus_one_linear_closed_exp eps0 heps0 in
  let Coq_existT (x1, a0) = s0 in
  let Coq_pair (_, a1) = a0 in
  let Coq_pair (r2, r3) = a1 in
  let a2 =
    real_mult x1
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
  in
  let b =
    real_mult x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xI Coq_xH))) })
  in
  let c = real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let delta = real_min (real_min a2 b) c in
  let h14T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let h112T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xI Coq_xH))) }
  in
  let h12T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let hA0 =
    b5dK_real_mult_positive_exp x1
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      r2
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) } h14T)
  in
  let hB0 =
    b5dK_real_mult_positive_exp x0
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xI Coq_xH))) })
      r0
      (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        (Coq_xO (Coq_xI Coq_xH))) } h112T)
  in
  let hC0 =
    b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
      Coq_xH) } h12T
  in
  let hdelta0 = real_min_pos (real_min a2 b) c (real_min_pos a2 b hA0 hB0) hC0
  in
  Coq_existT (delta, (Coq_pair (hdelta0, (fun h hh_UU03b4_ eps' heps' ->
  let hhAB = real_min_lt_l h (real_min a2 b) c hh_UU03b4_ in
  let hhA = real_min_lt_l h a2 b hhAB in
  let hhB = real_min_lt_r h a2 b hhAB in
  let hhC = real_min_lt_r h (real_min a2 b) c hh_UU03b4_ in
  let hactDu = b5f_Du_act_delta r x hxr h x0 r0 hhB hhC in
  let hlogS = fun epsL' hepsL' -> r1 h epsL' hepsL' hactDu in
  let hvlt = b5j_v_act_lt r x hxr h x1 r2 hlogS hhA hhC in
  let eps0' =
    real_mult
      (real_const { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) })
      (real_mult eps' invM)
  in
  let invE = real_inv_pos eps heps in
  let shV =
    real_mult
      (real_mult invE
        (real_const
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) } (b5j_Kvq r))))
      eps'
  in
  let h34T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      (Coq_xI Coq_xH)); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let h14KvT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) } (b5j_Kvq r))
  in
  let hinvE0 = real_inv_pos_pos eps heps in
  let heps0' =
    b5dK_real_mult_positive_exp
      (real_const { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden = (Coq_xO
        (Coq_xO Coq_xH)) })
      (real_mult eps' invM)
      (b5dM_real_const_pos { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
        (Coq_xO (Coq_xO Coq_xH)) } h34T)
      (b5dK_real_mult_positive_exp eps' invM heps' hinvM0)
  in
  let hshV =
    b5dK_real_mult_positive_exp
      (real_mult invE
        (real_const
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) } (b5j_Kvq r))))
      eps'
      (b5dK_real_mult_positive_exp invE
        (real_const
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) } (b5j_Kvq r)))
        hinvE0
        (b5dM_real_const_pos
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) } (b5j_Kvq r))
          h14KvT))
      heps'
  in
  let hvslope = b5j_v_abs_bd r x hxr h shV hshV hlogS hhC in
  let hlin =
    real_le_trans
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h)))))
      (real_abs
        (real_plus
          (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
          (real_opp (b5f_v x h))))
      (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
      (RealSetoid.real_eq_le
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h)))))
        (real_abs
          (real_plus
            (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
            (real_opp (b5f_v x h))))
        (real_abs_eq_compat
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))
          (real_plus
            (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
            (real_opp (b5f_v x h)))
          (b5j_lin_shape_eq (b5f_v x h))))
      (r3 (b5f_v x h) hvlt eps0' heps0')
  in
  let hmulv =
    real_le_trans (real_mult eps0 (real_abs (b5f_v x h)))
      (real_mult (real_abs (b5f_v x h)) eps0)
      (real_mult eps0
        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
      (RealSetoid.real_eq_le (real_mult eps0 (real_abs (b5f_v x h)))
        (real_mult (real_abs (b5f_v x h)) eps0)
        (real_mult_comm eps0 (real_abs (b5f_v x h))))
      (real_le_trans (real_mult (real_abs (b5f_v x h)) eps0)
        (real_mult
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          eps0)
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        (real_le_mult_compat_weak (real_abs (b5f_v x h))
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          eps0 heps0le hvslope)
        (RealSetoid.real_eq_le
          (real_mult
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
            eps0)
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          (real_mult_comm
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
            eps0)))
  in
  let hlin2 =
    real_le_trans
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h)))))
      (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
      (real_plus
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0')
      hlin
      (real_le_plus_compat (real_mult eps0 (real_abs (b5f_v x h)))
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0' eps0' hmulv (real_le_refl eps0'))
  in
  let hmid1 =
    real_le_trans
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h)))))
        (real_abs sx))
      (real_mult (real_abs sx)
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'))
      (RealSetoid.real_eq_le
        (real_mult (real_abs sx)
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h))))))
        (real_mult
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_abs sx))
        (real_mult_comm (real_abs sx)
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))))
      (real_le_trans
        (real_mult
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_abs sx))
        (real_mult
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0')
          (real_abs sx))
        (real_mult (real_abs sx)
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0'))
        (real_le_mult_compat_weak
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0')
          (real_abs sx)
          (RealSetoid.real_lt_le_iff_req real_zero (real_abs sx) (Coq_inl
            (b5j_Sx_abs_pos x)))
          hlin2)
        (RealSetoid.real_eq_le
          (real_mult
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0')
            (real_abs sx))
          (real_mult (real_abs sx)
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0'))
          (real_mult_comm
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0')
            (real_abs sx))))
  in
  let hreshape =
    RealSetoid.real_eq_mult_compat (real_abs sx)
      (real_plus
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0')
      (real_abs sx)
      (real_plus (real_mult (real_mult eps invM) (real_abs h))
        (real_mult eps' invM))
      (real_eq_refl (real_abs sx))
      (real_eq_trans
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0')
        (real_plus
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_mult eps0 shV))
          eps0')
        (real_plus (real_mult (real_mult eps invM) (real_abs h))
          (real_mult eps' invM))
        (RealSetoid.real_eq_plus_compat
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_mult eps0 shV))
          eps0'
          (b5j_mult_plus_distr_eq eps0
            (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          (real_eq_refl eps0'))
        (real_eq_trans
          (real_plus
            (real_plus
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult eps0 shV))
            eps0')
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_plus (real_mult eps0 shV) eps0'))
          (real_plus (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM))
          (real_eq_sym
            (real_plus
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_plus (real_mult eps0 shV) eps0'))
            (real_plus
              (real_plus
                (real_mult eps0
                  (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                (real_mult eps0 shV))
              eps0')
            (real_plus_assoc
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult eps0 shV) eps0'))
          (RealSetoid.real_eq_plus_compat
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_plus (real_mult eps0 shV) eps0')
            (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM)
            (real_eq_trans
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult (real_mult eps0 (real_const (b5j_Kvq r)))
                (real_abs h))
              (real_mult (real_mult eps invM) (real_abs h))
              (real_mult_assoc eps0 (real_const (b5j_Kvq r)) (real_abs h))
              (RealSetoid.real_eq_mult_compat
                (real_mult eps0 (real_const (b5j_Kvq r))) (real_abs h)
                (real_mult eps invM) (real_abs h)
                (b5j_eps0_kvq_req r eps invM) (real_eq_refl (real_abs h))))
            (real_eq_trans (real_plus (real_mult eps0 shV) eps0')
              (real_plus
                (real_mult
                  (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
                    (Coq_xO Coq_xH)) })
                  (real_mult eps' invM))
                (real_mult
                  (real_const { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                    (Coq_xO (Coq_xO Coq_xH)) })
                  (real_mult eps' invM)))
              (real_mult eps' invM)
              (RealSetoid.real_eq_plus_compat (real_mult eps0 shV) eps0'
                (real_mult
                  (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
                    (Coq_xO Coq_xH)) })
                  (real_mult eps' invM))
                (real_mult
                  (real_const { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
                    (Coq_xO (Coq_xO Coq_xH)) })
                  (real_mult eps' invM))
                (b5j_eps0_shv_req r eps eps' invM heps)
                (real_eq_refl
                  (real_mult
                    (real_const { coq_Qnum = (Zpos (Coq_xI Coq_xH));
                      coq_Qden = (Coq_xO (Coq_xO Coq_xH)) })
                    (real_mult eps' invM))))
              (b5j_fourth_threefourth_sum (real_mult eps' invM))))))
  in
  real_le_trans
    (real_abs
      (real_mult (b5a_S x)
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_mult (real_abs sx)
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_plus (real_mult eps (real_abs h)) eps')
    (RealSetoid.real_eq_le
      (real_abs
        (real_mult (b5a_S x)
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_abs_mult_req (b5a_S x)
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_le_trans
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult (real_abs sx)
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'))
      (real_plus (real_mult eps (real_abs h)) eps') hmid1
      (real_le_trans
        (real_mult (real_abs sx)
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0'))
        (real_mult (real_abs sx)
          (real_plus (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM)))
        (real_plus (real_mult eps (real_abs h)) eps')
        (RealSetoid.real_eq_le
          (real_mult (real_abs sx)
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0'))
          (real_mult (real_abs sx)
            (real_plus (real_mult (real_mult eps invM) (real_abs h))
              (real_mult eps' invM)))
          hreshape)
        (b5dK_real_abs_scaling_le_exp (b5a_S x) eps eps' h heps heps')))))))

(** val b5d4_const0_eq_zero : real_eq **)

let b5d4_const0_eq_zero =
  real_eq_of_zero_diff (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
    real_zero

(** val b5d4_S_const0_eq_one : real_eq **)

let b5d4_S_const0_eq_one =
  let h00 =
    real_eq_trans
      (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
        (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }))
      (real_mult real_zero real_zero) real_zero
      (RealSetoid.real_eq_mult_compat
        (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
        (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }) real_zero real_zero
        b5d4_const0_eq_zero b5d4_const0_eq_zero)
      (real_mult_zero real_zero)
  in
  let hone =
    real_eq_trans
      (real_plus real_one
        (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
          (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
      (real_plus real_one real_zero) real_one
      (RealSetoid.real_eq_plus_compat real_one
        (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
          (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }))
        real_one real_zero (real_eq_refl real_one) h00)
      (real_plus_zero real_one)
  in
  let hlog1 =
    real_log_wd
      (real_plus real_one
        (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
          (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
      real_one
      (b5a_one_plus_sq_pos (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }))
      real_lt_zero_one hone
  in
  let hlogz =
    real_eq_trans
      (real_log
        (real_plus real_one
          (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
            (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
        (b5a_one_plus_sq_pos
          (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
      (real_log real_one real_lt_zero_one) real_zero hlog1
      (real_log_one real_lt_zero_one)
  in
  let hmulz =
    real_eq_trans
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
          (b5a_one_plus_sq_pos
            (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }))))
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        real_zero)
      real_zero
      (RealSetoid.real_eq_mult_compat
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
          (b5a_one_plus_sq_pos
            (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        real_zero
        (real_eq_refl
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
        hlogz)
      (real_mult_zero
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
  in
  real_eq_trans
    (cauchy_real_exp
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
          (b5a_one_plus_sq_pos
            (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))))
    (cauchy_real_exp real_zero) real_one
    (cauchy_real_exp_wd
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })))
          (b5a_one_plus_sq_pos
            (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }))))
      real_zero hmulz)
    cauchy_real_exp_zero

(** val b5dE_const1_eq_one : real_eq **)

let b5dE_const1_eq_one =
  real_eq_of_zero_diff
    (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }) real_one

(** val b5dE_q_pos : coq_Q -> real_lt **)

let b5dE_q_pos q =
  real_const_pos q (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } q)

(** val b5dE_half_pos_real : real_lt **)

let b5dE_half_pos_real =
  real_const_pos
    (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
      (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
    (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
        (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))

(** val b5dE_log_ub_one : coq_Q -> real_lt **)

let b5dE_log_ub_one q =
  let t = real_mult (real_const q) (real_const q) in
  let e0 =
    coq_Qmult
      (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
        (coq_Qmult q q))
      { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let hteq = real_eq_of_zero_diff t (real_const (coq_Qmult q q)) in
  let heps0 =
    real_const_pos e0
      (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } e0)
  in
  let hlog1 =
    real_log_one_plus_le_eps t (real_const e0)
      (b5a_one_plus_sq_pos (real_const q)) heps0
  in
  let hle_t = RealSetoid.real_eq_le t (real_const (coq_Qmult q q)) hteq in
  let hle_sum =
    real_le_plus_compat t (real_const (coq_Qmult q q)) (real_const e0)
      (real_const e0) hle_t (real_le_refl (real_const e0))
  in
  let hsum_eq =
    real_eq_of_zero_diff
      (real_plus (real_const (coq_Qmult q q)) (real_const e0))
      (real_const (coq_Qplus (coq_Qmult q q) e0))
  in
  let hle_sum2 =
    real_le_trans (real_plus t (real_const e0))
      (real_plus (real_const (coq_Qmult q q)) (real_const e0))
      (real_const (coq_Qplus (coq_Qmult q q) e0)) hle_sum
      (RealSetoid.real_eq_le
        (real_plus (real_const (coq_Qmult q q)) (real_const e0))
        (real_const (coq_Qplus (coq_Qmult q q) e0)) hsum_eq)
  in
  let hlog2 =
    real_le_trans
      (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
      (real_plus t (real_const e0))
      (real_const (coq_Qplus (coq_Qmult q q) e0)) hlog1 hle_sum2
  in
  let hc_lt =
    real_const_lt (coq_Qplus (coq_Qmult q q) e0) { coq_Qnum = (Zpos Coq_xH);
      coq_Qden = Coq_xH }
  in
  real_le_lt_trans
    (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q)))
    (real_const (coq_Qplus (coq_Qmult q q) e0))
    (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }) hlog2 hc_lt

(** val b5dE_S_lt_exp_half : coq_Q -> real_lt **)

let b5dE_S_lt_exp_half q =
  let hlogb = b5dE_log_ub_one q in
  let hsmall =
    real_lt_eq_lt
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_log
          (real_plus real_one (real_mult (real_const q) (real_const q)))
          (b5a_one_plus_sq_pos (real_const q))))
      (real_mult
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (real_lt_mult_compat
        (real_log
          (real_plus real_one (real_mult (real_const q) (real_const q)))
          (b5a_one_plus_sq_pos (real_const q)))
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        b5dE_half_pos_real hlogb)
      (real_eq_of_zero_diff
        (real_mult
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
  in
  cauchy_real_exp_mono
    (real_mult
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (real_log
        (real_plus real_one (real_mult (real_const q) (real_const q)))
        (b5a_one_plus_sq_pos (real_const q))))
    (real_const
      (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } { coq_Qnum =
        (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
    hsmall

(** val b5dE_exp_half_le_two : real_le **)

let b5dE_exp_half_le_two =
  let hhalflt1 =
    real_lt_eq_lt
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }) real_one
      (real_const_lt
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
      b5dE_const1_eq_one
  in
  let he1 =
    real_exp_le_inv_one_minus
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      b5dE_half_pos_real hhalflt1
  in
  let w =
    real_lt_opp_plus
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      real_one hhalflt1
  in
  let hb =
    real_eq_of_zero_diff
      (real_plus real_one
        (real_opp
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))))
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
  in
  let hinvext =
    real_inv_pos_ext
      (real_plus real_one
        (real_opp
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))))
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      w b5dE_half_pos_real hb
  in
  let htwo =
    real_inv_unique
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (real_inv_pos
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        b5dE_half_pos_real)
      (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (real_inv_pos_correct
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        b5dE_half_pos_real)
      (real_eq_of_zero_diff
        (real_mult
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
          (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
            Coq_xH }))
        real_one)
  in
  real_le_trans
    (cauchy_real_exp
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
    (real_inv_pos
      (real_plus real_one
        (real_opp
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))))
      w)
    (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }) he1
    (real_le_trans
      (real_inv_pos
        (real_plus real_one
          (real_opp
            (real_const
              (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
                { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))))
        w)
      (real_inv_pos
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
        b5dE_half_pos_real)
      (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (RealSetoid.real_eq_le
        (real_inv_pos
          (real_plus real_one
            (real_opp
              (real_const
                (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
                  { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))))
          w)
        (real_inv_pos
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
          b5dE_half_pos_real)
        hinvext)
      (RealSetoid.real_eq_le
        (real_inv_pos
          (real_const
            (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
          b5dE_half_pos_real)
        (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
        htwo))

(** val b5dE_S_ub_tail_q : coq_Q -> (nat, __) sigT **)

let b5dE_S_ub_tail_q q =
  let s = b5a_S_ge_one (real_const q) (b5dE_q_pos q) in
  let Coq_existT (x, _) = s in
  let hstrict =
    real_lt_le_trans (b5a_S (real_const q))
      (cauchy_real_exp
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
      (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (b5dE_S_lt_exp_half q) b5dE_exp_half_le_two
  in
  let s0 =
    real_lt_pt_lt (b5a_S (real_const q))
      (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      hstrict
  in
  let Coq_existT (x0, _) = s0 in Coq_existT ((PeanoNat.Nat.max x x0), __)

(** val b5dH_E_eq_b5aE : coq_Real -> cw_unit -> real_eq **)

let b5dH_E_eq_b5aE x hx =
  real_eq_refl
    (real_plus (cauchy_real_sin (cauchy_real_arctan x hx))
      (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x hx)))))

(** val b5dH_J_zero0 : real_eq **)

let b5dH_J_zero0 =
  b5c_J_zero_at_zero b5c_unit_zero

(** val b5dH_E_zero_of_J_zero : coq_Real -> cw_unit -> real_eq -> real_eq **)

let b5dH_E_zero_of_J_zero x hx hJ0 =
  real_eq_trans (real_E x hx) (b5a_E x hx) real_zero (b5dH_E_eq_b5aE x hx)
    (b5p2_E_zero_of_J_zero x hx hJ0)

(** val b5dH_real_const_qeq : coq_Q -> coq_Q -> real_eq **)

let b5dH_real_const_qeq a b =
  real_eq_of_zero_diff (real_const a) (real_const b)

(** val b5dH_plus_const_eq : coq_Q -> coq_Q -> real_eq **)

let b5dH_plus_const_eq a b =
  real_eq_of_zero_diff (real_plus (real_const a) (real_const b))
    (real_const (coq_Qplus a b))

(** val b5dL_tkq : coq_Q -> nat -> nat -> coq_Q **)

let b5dL_tkq q m k =
  coq_Qdiv (coq_Qmult q { coq_Qnum = (Z.of_nat k); coq_Qden = Coq_xH })
    { coq_Qnum = (Z.of_nat m); coq_Qden = Coq_xH }

(** val b5dL_qdiv : coq_Q -> nat -> coq_Q **)

let b5dL_qdiv q m =
  coq_Qdiv q { coq_Qnum = (Z.of_nat m); coq_Qden = Coq_xH }

(** val b5dL_Qnsum : (nat -> coq_Q) -> nat -> coq_Q **)

let rec b5dL_Qnsum b = function
| O -> { coq_Qnum = Z0; coq_Qden = Coq_xH }
| S m -> coq_Qplus (b5dL_Qnsum b m) (b m)

(** val b5dL_tkC : coq_Q -> nat -> nat -> cw_unit **)

let b5dL_tkC q m k =
  b5c_const_unit (b5dL_tkq q m k)

(** val b5dL_abs_const : coq_Q -> real_eq **)

let b5dL_abs_const a =
  real_eq_of_zero_diff (real_abs (real_const a)) (real_const (coq_Qabs a))

(** val b5dL_mult_const : coq_Q -> coq_Q -> real_eq **)

let b5dL_mult_const a b =
  real_eq_of_zero_diff (real_mult (real_const a) (real_const b))
    (real_const (coq_Qmult a b))

(** val b5dL_bk : coq_Q -> nat -> coq_Q -> nat -> coq_Q **)

let b5dL_bk q m epsQ _ =
  coq_Qplus
    (coq_Qmult
      (coq_Qdiv epsQ
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH } q))
      (b5dL_qdiv q m))
    (coq_Qdiv epsQ
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
        Coq_xH } { coq_Qnum = (Z.of_nat m); coq_Qden = Coq_xH }))

(** val b5dL_epsQ1 : nat -> coq_Q -> coq_Q **)

let b5dL_epsQ1 m epsQ =
  coq_Qdiv epsQ
    (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
      Coq_xH } { coq_Qnum = (Z.of_nat m); coq_Qden = Coq_xH })

(** val b5dL_J_grid_premise :
    coq_Q -> nat -> (nat -> coq_Q) -> (nat -> coq_Q) -> (nat -> __ -> cw_unit
    -> cw_unit -> real_le) -> cw_unit -> cw_unit -> real_le **)

let b5dL_J_grid_premise q m b e hstep c0 cM =
  let rec f n cn c0' =
    match n with
    | O ->
      let hjw =
        b5p2_J_wd (real_const (b5dL_tkq q m O)) (real_const (b5dL_tkq q m O))
          cn c0' (real_eq_refl (real_const (b5dL_tkq q m O)))
      in
      real_le_trans
        (real_abs
          (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
        real_zero (real_const (coq_Qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
        (RealSetoid.real_eq_le
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
          real_zero
          (real_eq_trans
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) cn))))
            real_zero
            (real_abs_eq_compat
              (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))
              (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) cn)))
              (RealSetoid.real_eq_plus_compat
                (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))
                (b5c_J (real_const (b5dL_tkq q m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) cn))
                (real_eq_refl (b5c_J (real_const (b5dL_tkq q m O)) cn))
                (RealSetoid.real_eq_opp_compat
                  (b5c_J (real_const (b5dL_tkq q m O)) c0')
                  (b5c_J (real_const (b5dL_tkq q m O)) cn)
                  (real_eq_sym (b5c_J (real_const (b5dL_tkq q m O)) cn)
                    (b5c_J (real_const (b5dL_tkq q m O)) c0') hjw))))
            (real_eq_trans
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m O)) cn))))
              (real_abs real_zero) real_zero
              (real_abs_eq_compat
                (real_plus (b5c_J (real_const (b5dL_tkq q m O)) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m O)) cn)))
                real_zero
                (real_plus_opp (b5c_J (real_const (b5dL_tkq q m O)) cn)))
              real_abs_zero_req)))
        (RealSetoid.real_eq_le real_zero
          (real_const (coq_Qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
          (real_eq_sym
            (real_const (coq_Qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
            real_zero
            (real_eq_of_zero_diff
              (real_const (coq_Qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
              real_zero)))
    | S n0 ->
      let hmid = b5dL_tkC q m n0 in
      let hstep_n = hstep n0 __ hmid cn in
      let hih_n = f n0 hmid c0' in
      let htri =
        real_abs_triangle_le_eps
          (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid)))
          (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
            (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))
          (real_const (e n0))
          (real_const_pos (e n0)
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } (e n0)))
      in
      let hring =
        real_eq_of_zero_diff
          (real_plus
            (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid)))
            (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
              (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
          (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))
      in
      let hmain =
        RealSetoid.real_le_id_l
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
          (real_abs
            (real_plus
              (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid)))
              (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))))
          (real_plus
            (real_plus
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid))))
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))))
            (real_const (e n0)))
          (real_abs_eq_compat
            (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))
            (real_plus
              (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid)))
              (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
            (real_eq_sym
              (real_plus
                (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid)))
                (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
              (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))
              hring))
          htri
      in
      let hrhs =
        real_le_plus_compat
          (real_plus
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid))))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))))
          (real_plus (real_const (b n0))
            (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
          (real_const (e n0)) (real_const (e n0))
          (real_le_plus_compat
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid))))
            (real_const (b n0))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
            (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0)))
            hstep_n hih_n)
          (real_le_refl (real_const (e n0)))
      in
      real_le_trans
        (real_abs
          (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
        (real_plus
          (real_plus (real_const (b n0))
            (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
          (real_const (e n0)))
        (real_const (coq_Qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))
        (real_le_trans
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0'))))
          (real_plus
            (real_plus
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m n0)) hmid))))
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0')))))
            (real_const (e n0)))
          (real_plus
            (real_plus (real_const (b n0))
              (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
            (real_const (e n0)))
          hmain hrhs)
        (RealSetoid.real_eq_le
          (real_plus
            (real_plus (real_const (b n0))
              (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
            (real_const (e n0)))
          (real_const (coq_Qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))
          (real_eq_of_zero_diff
            (real_plus
              (real_plus (real_const (b n0))
                (real_const (coq_Qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
              (real_const (e n0)))
            (real_const
              (coq_Qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))))
  in f m cM c0

(** val b5dL_eps_real_lower :
    coq_Real -> real_lt -> (coq_Q, (coq_QltT, real_le) coq_And) sigT **)

let b5dL_eps_real_lower e = function
| Coq_existT (x, a) ->
  let Coq_pair (_, s) = a in
  let Coq_existT (x0, _) = s in
  Coq_existT
  ((coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }),
  (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
     (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })),
  (RealSetoid.real_lt_le_iff_req
    (real_const
      (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
    e (Coq_inl (Coq_existT
    ((coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }),
    (Coq_pair
    ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
       (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })),
    (Coq_existT (x0, (fun n _ ->
    qltT_eq_compat_r
      (coq_Qminus (projT1 e n)
        (projT1
          (real_const
            (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH }))
          n))
      (coq_Qminus (projT1 e n)
        (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }))
      (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      (coq_Qlt_to_QltT
        (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
        (coq_Qminus (projT1 e n)
          (coq_Qdiv x { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
            Coq_xH })))))))))))))))

(** val b5dL_J_zero_on_grid_premise :
    coq_Q -> nat -> coq_Q -> (nat -> __ -> cw_unit -> cw_unit -> real_le) ->
    cw_unit -> real_le **)

let b5dL_J_zero_on_grid_premise q m epsQ hstep hq =
  let c0 = b5dL_tkC q m O in
  let cM = b5dL_tkC q m m in
  let hgrid =
    b5dL_J_grid_premise q m (b5dL_bk q m epsQ) (fun _ -> b5dL_epsQ1 m epsQ)
      (fun k _ -> hstep k __) c0 cM
  in
  let hbrM =
    b5p2_J_wd (real_const (b5dL_tkq q m m)) (real_const q) cM hq
      (b5dH_real_const_qeq (b5dL_tkq q m m) q)
  in
  let hbr0 =
    b5p2_J_wd (real_const (b5dL_tkq q m O))
      (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH }) c0 b5c_unit_zero
      (b5dH_real_const_qeq (b5dL_tkq q m O) { coq_Qnum = Z0; coq_Qden =
        Coq_xH })
  in
  let habs =
    real_abs_eq_compat
      (real_plus (b5c_J (real_const q) hq)
        (real_opp
          (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
            b5c_unit_zero)))
      (real_plus (b5c_J (real_const (b5dL_tkq q m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0)))
      (RealSetoid.real_eq_plus_compat (b5c_J (real_const q) hq)
        (real_opp
          (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
            b5c_unit_zero))
        (b5c_J (real_const (b5dL_tkq q m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0))
        (real_eq_sym (b5c_J (real_const (b5dL_tkq q m m)) cM)
          (b5c_J (real_const q) hq) hbrM)
        (RealSetoid.real_eq_opp_compat
          (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
            b5c_unit_zero)
          (b5c_J (real_const (b5dL_tkq q m O)) c0)
          (real_eq_sym (b5c_J (real_const (b5dL_tkq q m O)) c0)
            (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              b5c_unit_zero)
            hbr0)))
  in
  real_le_trans
    (real_abs
      (real_plus (b5c_J (real_const q) hq)
        (real_opp
          (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
            b5c_unit_zero))))
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0))))
    (real_const epsQ)
    (RealSetoid.real_eq_le
      (real_abs
        (real_plus (b5c_J (real_const q) hq)
          (real_opp
            (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
              b5c_unit_zero))))
      (real_abs
        (real_plus (b5c_J (real_const (b5dL_tkq q m m)) cM)
          (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0))))
      habs)
    (RealSetoid.real_le_id_r
      (real_abs
        (real_plus (b5c_J (real_const (b5dL_tkq q m m)) cM)
          (real_opp (b5c_J (real_const (b5dL_tkq q m O)) c0))))
      (real_const
        (coq_Qplus (b5dL_Qnsum (b5dL_bk q m epsQ) m)
          (b5dL_Qnsum (fun _ -> b5dL_epsQ1 m epsQ) m)))
      (real_const epsQ)
      (b5dH_real_const_qeq
        (coq_Qplus (b5dL_Qnsum (b5dL_bk q m epsQ) m)
          (b5dL_Qnsum (fun _ -> b5dL_epsQ1 m epsQ) m))
        epsQ)
      hgrid)

(** val b5dL_E_rational_zero_premise :
    coq_Q -> (coq_Q -> __ -> (nat, (coq_NatLe, nat -> __ -> cw_unit ->
    cw_unit -> real_le) coq_And) sigT) -> cw_unit -> real_eq **)

let b5dL_E_rational_zero_premise q hmod hq =
  b5dH_E_zero_of_J_zero (real_const q) hq
    (b4_abs_le_forall_eps_eq (b5c_J (real_const q) hq) real_zero (fun e he ->
      let s = b5dL_eps_real_lower e he in
      let Coq_existT (x, a) = s in
      let Coq_pair (_, r) = a in
      let s0 = hmod x __ in
      let Coq_existT (x0, a0) = s0 in
      let Coq_pair (_, r0) = a0 in
      let hle_c = b5dL_J_zero_on_grid_premise q x0 x r0 hq in
      let habs0 =
        real_abs_eq_compat
          (real_plus (b5c_J (real_const q) hq) (real_opp real_zero))
          (real_plus (b5c_J (real_const q) hq)
            (real_opp
              (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
                b5c_unit_zero)))
          (RealSetoid.real_eq_plus_compat (b5c_J (real_const q) hq)
            (real_opp real_zero) (b5c_J (real_const q) hq)
            (real_opp
              (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
                b5c_unit_zero))
            (real_eq_refl (b5c_J (real_const q) hq))
            (RealSetoid.real_eq_opp_compat real_zero
              (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
                b5c_unit_zero)
              (real_eq_sym
                (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
                  b5c_unit_zero)
                real_zero b5dH_J_zero0)))
      in
      real_le_trans
        (real_abs (real_plus (b5c_J (real_const q) hq) (real_opp real_zero)))
        (real_const x) e
        (RealSetoid.real_le_id_l
          (real_abs
            (real_plus (b5c_J (real_const q) hq) (real_opp real_zero)))
          (real_abs
            (real_plus (b5c_J (real_const q) hq)
              (real_opp
                (b5c_J (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
                  b5c_unit_zero))))
          (real_const x) habs0 hle_c)
        r))

(** val b5dP_S_diff_closed_r_M_exp_tail :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> coq_Real ->
    real_lt -> (coq_Real, (real_lt, coq_Real -> real_lt -> coq_Real ->
    real_lt -> real_le) coq_And) sigT **)

let b5dP_S_diff_closed_r_M_exp_tail r x hxr m nM eps heps =
  let k2 =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
        coq_Qden = Coq_xH }
        (coq_Qplus m { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let k2p =
    coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
        coq_Qden = Coq_xH }
        (coq_Qplus m { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
  in
  let hk2T = b5l_k_posT m in
  let hk2pT = b5l_k_posT m in
  let h2T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let h4T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }
  in
  let h8T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO Coq_xH))) }
  in
  let h16T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
      Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let eps1 =
    real_mult eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
  in
  let heps1 =
    real_mult_positive eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
      heps
      (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        Coq_xH) } h2T)
  in
  let eps2 =
    real_mult eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
  in
  let heps2 =
    real_mult_positive eps
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      heps
      (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) } h4T)
  in
  let s = b5dK_exp_part_bound_closed_r_exp r x hxr eps1 heps1 in
  let Coq_existT (x0, a) = s in
  let Coq_pair (r0, r1) = a in
  let s0 = b5dK_gdiff_pts_r_exp r x hxr eps2 heps2 k2 k2p hk2T hk2pT in
  let Coq_existT (x1, a0) = s0 in
  let Coq_pair (r2, s1) = a0 in
  let delta = real_min x0 x1 in
  let hd0 = real_min_pos x0 x1 r0 r2 in
  Coq_existT (delta, (Coq_pair (hd0, (fun h hh eps' heps' ->
  let s2 = b5n_eps_proj_lt eps heps in
  let Coq_existT (_, a1) = s2 in
  let Coq_pair (_, s3) = a1 in
  let Coq_existT (x2, _) = s3 in
  let hhE = real_min_lt_l h x0 x1 hh in
  let hhG = real_min_lt_r h x0 x1 hh in
  let s4 = b5n_eps_proj_lt eps' heps' in
  let Coq_existT (x3, a2) = s4 in
  let Coq_pair (_, s5) = a2 in
  let Coq_existT (x4, _) = s5 in
  let eta =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) } x3
  in
  let hetaT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } x3)
  in
  let eps1' =
    real_mult eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
  in
  let heps1' =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) })
      heps'
      (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        Coq_xH)) } h4T)
  in
  let shE =
    real_mult eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
  in
  let hshE =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
      heps'
      (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) } h16T)
  in
  let eps2' =
    real_mult eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) })
  in
  let heps2' =
    real_mult_positive eps'
      (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) })
      heps'
      (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } h8T)
  in
  let m0 =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH))))) } x3
  in
  let hm0T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) } x3)
  in
  let err =
    real_plus (b5a_S (real_plus x h))
      (real_opp
        (real_plus (b5a_S x)
          (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))
  in
  let eobj =
    real_mult (b5a_S x)
      (real_plus (cauchy_real_exp (b5f_v x h))
        (real_opp (real_plus real_one (b5f_v x h))))
  in
  let wS =
    real_plus (b5f_v x h)
      (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))
  in
  let gob = real_mult (b5a_S x) wS in
  let bexp = real_plus (real_mult eps1 (real_abs h)) eps1' in
  let hexp_le = r1 h hhE eps1' heps1' in
  let s6 = b5i_abs_le_pointwise eobj bexp hexp_le shE hshE in
  let Coq_existT (x5, _) = s6 in
  let s7 = s1 h hhG eps2' heps2' in
  let Coq_existT (x6, _) = s7 in
  let s8 = b5l_eq_abs_tri err eobj gob m0 (b5f_S_err_decomp x h) hm0T in
  let Coq_existT (x7, _) = s8 in
  Coq_inl (Coq_existT (eta, (Coq_pair (hetaT,
  (let nmax =
     PeanoNat.Nat.max nM
       (PeanoNat.Nat.max x2
         (PeanoNat.Nat.max x4 (PeanoNat.Nat.max x5 (PeanoNat.Nat.max x6 x7))))
   in
   Coq_existT (nmax, (fun n _ ->
   coq_Qlt_to_QltT eta
     (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1 (real_abs err) n)))))))))))))

(** val b5dQ_min_lb :
    coq_Real -> coq_Real -> coq_Real -> real_lt -> real_lt -> real_lt **)

let b5dQ_min_lb lb a b hltA hltB =
  let Coq_existT (x, a0) = hltA in
  let Coq_pair (_, s) = a0 in
  let Coq_existT (x0, _) = s in
  let Coq_existT (x1, a1) = hltB in
  let Coq_pair (_, s0) = a1 in
  let Coq_existT (x2, _) = s0 in
  let e = coq_Qmin x x1 in
  let he = coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } e in
  Coq_existT (e, (Coq_pair (he, (Coq_existT ((PeanoNat.Nat.max x0 x2),
  (fun n _ ->
  coq_Qlt_to_QltT e (coq_Qminus (projT1 (real_min a b) n) (projT1 lb n))))))))

(** val b5dQ_Hq32T : coq_QltT **)

let b5dQ_Hq32T =
  Coq_id_refl

(** val b5dQ_chain3 : coq_Q -> coq_Q **)

let b5dQ_chain3 a =
  coq_Qmult
    (coq_Qmult a { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) })
    { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }

(** val b5dQ_chain4 : coq_Q -> coq_Q **)

let b5dQ_chain4 a =
  coq_Qmult (b5dQ_chain3 a) { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))))))))) }

(** val b5dQ_vB : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_vB q a =
  coq_Qmin
    (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
      (coq_Qminus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } q))
    (coq_Qmult (b5dQ_chain4 a)
      (coq_Qinv
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO Coq_xH))); coq_Qden =
          Coq_xH }
          (coq_Qplus
            (b3rr_C2
              (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
                Coq_xH) }
                (coq_Qplus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } q)))
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))))

(** val b5dQ_margin_lemma : coq_Q -> coq_QltT **)

let b5dQ_margin_lemma v =
  coq_Qlt_to_QltT
    (coq_Qmult v { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      Coq_xH)) })
    (coq_Qminus v
      (coq_Qmult v { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))

(** val b5dQ_vSC : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_vSC q a =
  coq_Qmin
    (coq_Qmin
      (coq_Qmin (b5dQ_vB q a) { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
        Coq_xH) })
      (coq_Qmult (b5dQ_chain3 a) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xI Coq_xH)))))))))) }))
    (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      Coq_xH)) }
      (coq_Qinv
        (coq_Qplus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          (coq_Qmult (b5dQ_chain3 a) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))))))))) }))))

(** val b5dQ_vE : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_vE q a =
  coq_Qmin (coq_Qmin (b5dQ_vSC q a) (b5dQ_vSC q a))
    (coq_Qmult
      (coq_Qmult a { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) })
      { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))) })

(** val b5dQ_lb_E :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> real_lt **)

let b5dQ_lb_E q _ _ a =
  Coq_existT
    ((coq_Qmult (b5dQ_vE q a) { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
       (Coq_xO Coq_xH)) }),
    (Coq_pair
    ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
       (coq_Qmult (b5dQ_vE q a) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
         (Coq_xO (Coq_xO Coq_xH)) })),
    (Coq_existT (O, (fun _ _ -> b5dQ_margin_lemma (b5dQ_vE q a)))))))

(** val b5dQ_Hq14T : coq_QltT **)

let b5dQ_Hq14T =
  coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
    Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }

(** val b5dQ_Hq1T : coq_QltT **)

let b5dQ_Hq1T =
  coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum = (Zpos
    Coq_xH); coq_Qden = Coq_xH }

(** val b5dQ_S_tk0_eq_one : coq_Q -> nat -> real_eq **)

let b5dQ_S_tk0_eq_one q m =
  real_eq_trans (b5a_S (real_const (b5dL_tkq q m O)))
    (b5a_S (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })) real_one
    (b5m_S_wd (real_const (b5dL_tkq q m O))
      (real_const { coq_Qnum = Z0; coq_Qden = Coq_xH })
      (b5dH_real_const_qeq (b5dL_tkq q m O) { coq_Qnum = Z0; coq_Qden =
        Coq_xH }))
    b5d4_S_const0_eq_one

(** val b5dQ_S_lb_tail_k0 : coq_Q -> nat -> (nat, __) sigT **)

let b5dQ_S_lb_tail_k0 q m =
  let s =
    b5dQ_S_tk0_eq_one q m { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
      (Coq_xO Coq_xH)) } b5dQ_Hq14T
  in
  let Coq_existT (x, _) = s in Coq_existT (x, __)

(** val b5dQ_S_ub_tail_k0 : coq_Q -> nat -> (nat, __) sigT **)

let b5dQ_S_ub_tail_k0 q m =
  let s =
    b5dQ_S_tk0_eq_one q m { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
      b5dQ_Hq1T
  in
  let Coq_existT (x, _) = s in Coq_existT (x, __)

(** val b5dQ_S_ub_tail_restate :
    (nat -> coq_Q) -> (nat, __) sigT -> (nat, __) sigT **)

let b5dQ_S_ub_tail_restate _ = function
| Coq_existT (x, _) -> Coq_existT (x, __)

(** val b5dQ_S_lb_tail_kS : coq_Q -> nat -> nat -> (nat, __) sigT **)

let b5dQ_S_lb_tail_kS q m k =
  b5dQ_S_ub_tail_restate (fun n ->
    projT1 (b5a_S (real_const (b5dL_tkq q m k))) n)
    (b5a_S_ge_one (real_const (b5dL_tkq q m k))
      (real_const_pos_f1 (b5dL_tkq q m k)))

(** val b5dQ_S_ub_tail_kS : coq_Q -> nat -> nat -> (nat, __) sigT **)

let b5dQ_S_ub_tail_kS q m k =
  b5dE_S_ub_tail_q (b5dL_tkq q m k)

(** val b5dQ_tkq_Hxr : coq_Q -> nat -> nat -> nat -> coq_QleT' **)

let b5dQ_tkq_Hxr q m k n =
  coq_Qle_to_QleT' (coq_Qabs (projT1 (real_const (b5dL_tkq q m k)) n)) q

(** val b5dQ_xph_unit : coq_Q -> nat -> nat -> cw_unit **)

let b5dQ_xph_unit q m k n =
  coq_Qle_to_QleT'
    (coq_Qabs
      (projT1
        (real_plus (real_const (b5dL_tkq q m k)) (real_const (b5dL_qdiv q m)))
        n))
    { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }

(** val b5dQ_rhs_bk : coq_Q -> nat -> nat -> coq_Q -> real_eq **)

let b5dQ_rhs_bk q m k epsQ =
  let heta =
    real_eq_trans (real_abs (real_const (b5dL_qdiv q m)))
      (real_const (coq_Qabs (b5dL_qdiv q m))) (real_const (b5dL_qdiv q m))
      (b5dL_abs_const (b5dL_qdiv q m))
      (b5dH_real_const_qeq (coq_Qabs (b5dL_qdiv q m)) (b5dL_qdiv q m))
  in
  let hm =
    real_eq_trans
      (real_mult
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_abs (real_const (b5dL_qdiv q m))))
      (real_mult
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_const (b5dL_qdiv q m)))
      (real_const
        (coq_Qmult
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q))
          (b5dL_qdiv q m)))
      (RealSetoid.real_eq_mult_compat
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_abs (real_const (b5dL_qdiv q m)))
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_const (b5dL_qdiv q m))
        (real_eq_refl
          (real_const
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q))))
        heta)
      (b5dL_mult_const
        (coq_Qdiv epsQ
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }
            q))
        (b5dL_qdiv q m))
  in
  real_eq_trans
    (real_plus
      (real_mult
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_abs (real_const (b5dL_qdiv q m))))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_plus
      (real_const
        (coq_Qmult
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q))
          (b5dL_qdiv q m)))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_const (b5dL_bk q m epsQ k))
    (RealSetoid.real_eq_plus_compat
      (real_mult
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_abs (real_const (b5dL_qdiv q m))))
      (real_const (b5dL_epsQ1 m epsQ))
      (real_const
        (coq_Qmult
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q))
          (b5dL_qdiv q m)))
      (real_const (b5dL_epsQ1 m epsQ)) hm
      (real_eq_refl (real_const (b5dL_epsQ1 m epsQ))))
    (real_eq_trans
      (real_plus
        (real_const
          (coq_Qmult
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q))
            (b5dL_qdiv q m)))
        (real_const (b5dL_epsQ1 m epsQ)))
      (real_const
        (coq_Qplus
          (coq_Qmult
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q))
            (b5dL_qdiv q m))
          (b5dL_epsQ1 m epsQ)))
      (real_const (b5dL_bk q m epsQ k))
      (b5dH_plus_const_eq
        (coq_Qmult
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q))
          (b5dL_qdiv q m))
        (b5dL_epsQ1 m epsQ))
      (real_eq_refl (real_const (b5dL_bk q m epsQ k))))

(** val b5dQ_J_tk_succ_bridge :
    coq_Q -> nat -> nat -> cw_unit -> cw_unit -> real_eq **)

let b5dQ_J_tk_succ_bridge q m k hk1 hp =
  b5p2_J_wd (real_const (b5dL_tkq q m (S k)))
    (real_plus (real_const (b5dL_tkq q m k)) (real_const (b5dL_qdiv q m)))
    hk1 hp
    (real_eq_trans (real_const (b5dL_tkq q m (S k)))
      (real_const (coq_Qplus (b5dL_tkq q m k) (b5dL_qdiv q m)))
      (real_plus (real_const (b5dL_tkq q m k)) (real_const (b5dL_qdiv q m)))
      (b5dH_real_const_qeq (b5dL_tkq q m (S k))
        (coq_Qplus (b5dL_tkq q m k) (b5dL_qdiv q m)))
      (real_eq_sym
        (real_plus (real_const (b5dL_tkq q m k)) (real_const (b5dL_qdiv q m)))
        (real_const (coq_Qplus (b5dL_tkq q m k) (b5dL_qdiv q m)))
        (b5dH_plus_const_eq (b5dL_tkq q m k) (b5dL_qdiv q m))))

(** val b5dQ_J_cert_wd : coq_Q -> cw_unit -> cw_unit -> real_eq **)

let b5dQ_J_cert_wd t hx hx' =
  b5p2_J_wd (real_const t) (real_const t) hx hx' (real_eq_refl (real_const t))

(** val b5dQ_step_inst :
    coq_Q -> nat -> nat -> (nat -> coq_QleT') -> cw_unit -> cw_unit ->
    cw_unit -> coq_Real -> real_le -> real_le **)

let b5dQ_step_inst q m k hxr hk1 hk hxh r hmain =
  RealSetoid.real_le_id_l
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q m k)) hk))))
    (real_abs
      (real_plus
        (b5c_J
          (real_plus (real_const (b5dL_tkq q m k))
            (real_const (b5dL_qdiv q m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q m k)) q hxr)))))
    r
    (real_abs_eq_compat
      (real_plus (b5c_J (real_const (b5dL_tkq q m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q m k)) hk)))
      (real_plus
        (b5c_J
          (real_plus (real_const (b5dL_tkq q m k))
            (real_const (b5dL_qdiv q m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q m k)) q hxr))))
      (RealSetoid.real_eq_plus_compat
        (b5c_J (real_const (b5dL_tkq q m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q m k)) hk))
        (b5c_J
          (real_plus (real_const (b5dL_tkq q m k))
            (real_const (b5dL_qdiv q m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q m k)) q hxr)))
        (b5dQ_J_tk_succ_bridge q m k hk1 hxh)
        (RealSetoid.real_eq_opp_compat
          (b5c_J (real_const (b5dL_tkq q m k)) hk)
          (b5c_J (real_const (b5dL_tkq q m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q m k)) q hxr))
          (b5dQ_J_cert_wd (b5dL_tkq q m k) hk
            (b3rr_dom_r1 (real_const (b5dL_tkq q m k)) q hxr)))))
    hmain

(** val b5dQ_lbSdiff_cE : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_lbSdiff_cE q a =
  coq_Qmin
    (coq_Qmin
      (coq_Qmult
        (coq_Qmin { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
          (coq_Qmult
            (coq_Qmult
              (coq_Qmult
                (coq_Qmult a { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
                  Coq_xH) })
                (coq_Qinv (b5j_Kvq q)))
              { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xI Coq_xH) })
            { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) }))
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO Coq_xH)) })
      (coq_Qmult
        (coq_Qmin { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) } b5j_kL))
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xI
        Coq_xH))) }))
    { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }

(** val b5dQ_lbSdiff_cG : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_lbSdiff_cG _ a =
  coq_Qmin
    (coq_Qmin
      (coq_Qmult
        (coq_Qmin { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
          (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            Coq_xH)) }
            (coq_Qmult
              (coq_Qmult a { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
                (Coq_xO Coq_xH)) })
              (coq_Qmult
                (coq_Qinv
                  (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO
                    Coq_xH)))); coq_Qden = Coq_xH }
                    (coq_Qplus { coq_Qnum = (Zpos (Coq_xO Coq_xH));
                      coq_Qden = Coq_xH } { coq_Qnum = (Zpos Coq_xH);
                      coq_Qden = Coq_xH })))
                { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))))
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xI
        Coq_xH))) })
      (coq_Qmult
        (coq_Qmult a { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
          Coq_xH)) })
        (coq_Qmult
          (coq_Qinv
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
              coq_Qden = Coq_xH }
              (coq_Qplus { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })))
    { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }

(** val b5dQ_lbSdiff_cS : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_lbSdiff_cS q a =
  coq_Qmin (b5dQ_lbSdiff_cE q a) (b5dQ_lbSdiff_cG q a)

(** val b5dQ_lbSdiff_val : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_lbSdiff_val q a =
  coq_Qmult (b5dQ_lbSdiff_cS q a) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
    (Coq_xO Coq_xH) }

(** val b5dQ_lb_Sdiff :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> real_lt **)

let b5dQ_lb_Sdiff q x hxr a nub =
  let cS = b5dQ_lbSdiff_cS q a in
  let lb =
    coq_Qmult cS { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let e =
    coq_Qmult lb { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  Coq_existT (e, (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } e), (Coq_existT
  (nub, (fun n _ ->
  coq_Qlt_to_QltT e
    (coq_Qminus
      (projT1
        (projT1
          (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
            Coq_xH)); coq_Qden = Coq_xH } nub (real_const a)
            (real_const_pos a
              (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } a))))
        n)
      (projT1 (real_const (b5dQ_lbSdiff_val q a)) n))))))))

(** val b5dQ_tau : coq_Q -> coq_Q **)

let b5dQ_tau q =
  coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
    (coq_Qinv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
        coq_Qden = Coq_xH }
        (coq_Qplus
          (coq_Qmult q { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
            Coq_xH })
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })))

(** val b5dQ_kS : coq_Q -> coq_Q **)

let b5dQ_kS q =
  coq_Qmult
    (coq_Qmult
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
        (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
      { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) })
    (coq_Qinv
      (coq_Qplus
        (coq_Qplus { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          (coq_Qmult q { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))

(** val b5dQ_m4 : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_m4 q epsQ =
  coq_Qmin
    (coq_Qmin
      (coq_Qmin
        (coq_Qmult
          (b5dQ_vE q
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q)))
          { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
        (b5dQ_lbSdiff_val q
          (coq_Qmult
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q))
            (b5dQ_kS q))))
      (b5dQ_lbSdiff_val q { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
    (b5dQ_tau q)

(** val b5dQ_delta0 : coq_Q -> coq_Q -> coq_Q **)

let b5dQ_delta0 q epsQ =
  coq_Qmult (b5dQ_m4 q epsQ) { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
    Coq_xH) }

(** val b5dQ_p4g_leaf_E :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> real_lt **)

let b5dQ_p4g_leaf_E =
  b5dQ_lb_E

(** val b5dQ_p4g_leaf_S :
    coq_Q -> coq_Real -> (nat -> coq_QleT') -> coq_Q -> nat -> real_lt **)

let b5dQ_p4g_leaf_S =
  b5dQ_lb_Sdiff

(** val b5dQ_p4g_J_tail_lb_var :
    coq_Q -> coq_Q -> nat -> nat -> (nat -> coq_QleT') -> nat -> nat ->
    (coq_Real, (real_lt, (coq_Real -> real_lt -> (nat -> coq_QleT') ->
    coq_Real -> real_lt -> real_le, real_lt) coq_And) coq_And) sigT **)

let b5dQ_p4g_J_tail_lb_var q epsQ mg k hxr nA nM =
  let x = real_const (b5dL_tkq q mg k) in
  let a =
    coq_Qdiv epsQ
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH } q)
  in
  let cA = { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) } in
  let m = { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH } in
  let ms = { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } in
  let mc = { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH } in
  let eps = real_const a in
  let heps =
    real_const_pos a (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } a)
  in
  let hx = b3rr_dom_r1 x q hxr in
  let cB =
    coq_Qmult cA { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }
  in
  let mE = coq_Qplus ms (coq_Qmult q mc) in
  let kE =
    coq_Qmult cB { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO Coq_xH))) }
  in
  let kEp =
    coq_Qmult cB { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let kapE =
    coq_Qmult cB { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let invM1 =
    coq_Qinv (coq_Qplus mE { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
  in
  let kS =
    coq_Qmult
      (coq_Qmult (coq_Qmult cA cB) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
        (Coq_xO (Coq_xO (Coq_xO Coq_xH))) })
      invM1
  in
  let kSp =
    coq_Qmult
      (coq_Qmult (coq_Qmult cA cB) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) })
      invM1
  in
  let kapS =
    coq_Qmult
      (coq_Qmult (coq_Qmult cA cB) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) })
      invM1
  in
  let k1 =
    coq_Qplus (coq_Qmult q m) { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
  in
  let tau =
    coq_Qmult cA
      (coq_Qinv
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
          coq_Qden = Coq_xH } k1))
  in
  let mu =
    coq_Qmult cA { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let kapS2 =
    coq_Qmult cA { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))) }
  in
  let hkEpT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult cB { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
  in
  let hkapET =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult cB { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
  in
  let hkSpT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult
        (coq_Qmult (coq_Qmult cA cB) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) })
        invM1)
  in
  let hkapST =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult
        (coq_Qmult (coq_Qmult cA cB) { coq_Qnum = (Zpos Coq_xH); coq_Qden =
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) })
        invM1)
  in
  let htauT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult cA
        (coq_Qinv
          (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))));
            coq_Qden = Coq_xH } k1)))
  in
  let hmuT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult cA { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
  in
  let hkapS2T =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult cA { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO Coq_xH)))) })
  in
  let epsE = real_mult eps (real_const kE) in
  let epsS = real_const (coq_Qmult a kS) in
  let _UU03b4_E =
    projT1
      (b5dI_E_diff_closed_r_exp q x hxr { coq_Qnum = (Zpos Coq_xH);
        coq_Qden = Coq_xH } { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
        b5d3_exp_arch4_C b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all epsE
        (b5dI_real_mult_positive_exp (real_const a)
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) })
          (b5dM_real_const_pos a
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } a))
          (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
            (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) } b5dQ_Hq32T)))
  in
  let h_UU03b4_E0 =
    fst
      (projT2
        (b5dI_E_diff_closed_r_exp q x hxr { coq_Qnum = (Zpos Coq_xH);
          coq_Qden = Coq_xH } { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          b5d3_exp_arch4_C b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all epsE
          (b5dI_real_mult_positive_exp (real_const a)
            (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
              (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) })
            (b5dM_real_const_pos a
              (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } a))
            (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden =
              (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) }
              b5dQ_Hq32T))))
  in
  let h_UU03b4_E =
    snd
      (projT2
        (b5dI_E_diff_closed_r_exp q x hxr { coq_Qnum = (Zpos Coq_xH);
          coq_Qden = Coq_xH } { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          b5d3_exp_arch4_C b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all epsE
          (b5dI_real_mult_positive_exp (real_const a)
            (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO
              (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) })
            (b5dM_real_const_pos a
              (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } a))
            (b5dM_real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden =
              (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) }
              b5dQ_Hq32T))))
  in
  let _UU03b4_S1 =
    projT1
      (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
        Coq_xH)); coq_Qden = Coq_xH } nM epsS
        (real_const_pos (coq_Qmult a kS)
          (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
            (coq_Qmult a kS))))
  in
  let h_UU03b4_S10 =
    fst
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
          Coq_xH)); coq_Qden = Coq_xH } nM epsS
          (real_const_pos (coq_Qmult a kS)
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
              (coq_Qmult a kS)))))
  in
  let h_UU03b4_S1 =
    snd
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
          Coq_xH)); coq_Qden = Coq_xH } nM epsS
          (real_const_pos (coq_Qmult a kS)
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
              (coq_Qmult a kS)))))
  in
  let _UU03b4_S2 =
    projT1
      (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
        Coq_xH)); coq_Qden = Coq_xH } nM
        (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
        (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } { coq_Qnum =
            (Zpos Coq_xH); coq_Qden = Coq_xH })))
  in
  let h_UU03b4_S20 =
    fst
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
          Coq_xH)); coq_Qden = Coq_xH } nM
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
          (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))))
  in
  let h_UU03b4_S2 =
    snd
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q x hxr { coq_Qnum = (Zpos (Coq_xO
          Coq_xH)); coq_Qden = Coq_xH } nM
          (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
          (real_const_pos { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
              { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))))
  in
  let delta =
    real_min (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau)
  in
  let hdpos =
    real_min_pos (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau)
      (real_min_pos (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2
        (real_min_pos _UU03b4_E _UU03b4_S1 h_UU03b4_E0 h_UU03b4_S10)
        h_UU03b4_S20)
      (real_const_pos tau htauT)
  in
  Coq_existT (delta, (Coq_pair (hdpos, (Coq_pair ((fun h hh hxh eps' heps' ->
  let s = b5dM_b5n_eps_proj_lt eps heps in
  let Coq_existT (_, a0) = s in
  let Coq_pair (_, s0) = a0 in
  let Coq_existT (x0, _) = s0 in
  let hh1 =
    real_min_lt_l h (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau) hh
  in
  let hh_UU03c4_ =
    real_min_lt_r h (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau) hh
  in
  let hh2 = real_min_lt_l h (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2 hh1 in
  let hhS2 = real_min_lt_r h (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2 hh1 in
  let hhE = real_min_lt_l h _UU03b4_E _UU03b4_S1 hh2 in
  let hhS1 = real_min_lt_r h _UU03b4_E _UU03b4_S1 hh2 in
  let s1 = b5dM_b5n_eps_proj_lt eps' heps' in
  let Coq_existT (x1, a1) = s1 in
  let Coq_pair (_, s2) = a1 in
  let Coq_existT (x2, _) = s2 in
  let eta =
    coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))) } x1
  in
  let hetaT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qmult { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO (Coq_xO
        (Coq_xO Coq_xH))) } x1)
  in
  let epsE' = real_mult eps' (real_const kEp) in
  let hepsE' =
    real_mult_positive eps' (real_const kEp) heps' (real_const_pos kEp hkEpT)
  in
  let shE = real_mult eps' (real_const kapE) in
  let hshE =
    real_mult_positive eps' (real_const kapE) heps'
      (real_const_pos kapE hkapET)
  in
  let epsS' = real_mult eps' (real_const kSp) in
  let hepsS' =
    real_mult_positive eps' (real_const kSp) heps' (real_const_pos kSp hkSpT)
  in
  let shS = real_mult eps' (real_const kapS) in
  let hshS =
    real_mult_positive eps' (real_const kapS) heps'
      (real_const_pos kapS hkapST)
  in
  let hc_UU03bc_ = real_const_pos mu hmuT in
  let hc_UU03ba_S2 = real_const_pos kapS2 hkapS2T in
  let bE = real_plus (real_mult epsE (real_abs h)) epsE' in
  let s3 =
    b5i_abs_le_pointwise (b5e_E_err x hx h hxh) bE
      (h_UU03b4_E h hhE hxh epsE' hepsE') shE hshE
  in
  let Coq_existT (x3, _) = s3 in
  let bS1 = real_plus (real_mult epsS (real_abs h)) epsS' in
  let s4 =
    b5i_abs_le_pointwise (b5m_rS x h) bS1 (h_UU03b4_S1 h hhS1 epsS' hepsS')
      shS hshS
  in
  let Coq_existT (x4, _) = s4 in
  let bS2 =
    real_plus
      (real_mult (real_const { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
        (real_abs h))
      (real_const mu)
  in
  let s5 =
    b5i_abs_le_pointwise (b5m_rS x h) bS2
      (h_UU03b4_S2 h hhS2 (real_const mu) hc_UU03bc_) (real_const kapS2)
      hc_UU03ba_S2
  in
  let Coq_existT (x5, _) = s5 in
  let s6 = b5i_h_le_const h tau hh_UU03c4_ htauT in
  let Coq_existT (x6, _) = s6 in
  let s7 = b5dM_b5c_d_proj_le_one x in
  let Coq_existT (x7, _) = s7 in
  let s8 = b5m_J_dec_proj x h hx hxh in
  let Coq_existT (x8, _) = s8 in
  let nmax =
    PeanoNat.Nat.max nM
      (PeanoNat.Nat.max (PeanoNat.Nat.max x0 x2)
        (PeanoNat.Nat.max (PeanoNat.Nat.max x8 x6)
          (PeanoNat.Nat.max (PeanoNat.Nat.max x3 (PeanoNat.Nat.max x4 x5))
            (PeanoNat.Nat.max nA x7))))
  in
  Coq_inl (Coq_existT (eta, (Coq_pair (hetaT, (Coq_existT (nmax, (fun n _ ->
  coq_Qlt_to_QltT eta
    (coq_Qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1
        (real_abs
          (real_plus (b5c_J (real_plus x h) hxh) (real_opp (b5c_J x hx))))
        n)))))))))),
  (let hqE =
     real_const_lt (b5dQ_delta0 q epsQ)
       (coq_Qmult
         (b5dQ_vE q
           (coq_Qdiv epsQ
             (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
               Coq_xH } q)))
         { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) })
   in
   let hlbE =
     b5dQ_p4g_leaf_E q x hxr
       (coq_Qdiv epsQ
         (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }
           q))
   in
   let hdE =
     real_lt_trans (real_const (b5dQ_delta0 q epsQ))
       (real_const
         (coq_Qmult
           (b5dQ_vE q
             (coq_Qdiv epsQ
               (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                 Coq_xH } q)))
           { coq_Qnum = (Zpos Coq_xH); coq_Qden = (Coq_xO Coq_xH) }))
       _UU03b4_E hqE hlbE
   in
   let hqS1 =
     real_const_lt (b5dQ_delta0 q epsQ)
       (b5dQ_lbSdiff_val q
         (coq_Qmult
           (coq_Qdiv epsQ
             (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
               Coq_xH } q))
           (b5dQ_kS q)))
   in
   let hlbS1 =
     b5dQ_p4g_leaf_S q x hxr
       (coq_Qmult
         (coq_Qdiv epsQ
           (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
             Coq_xH } q))
         (b5dQ_kS q))
       nM
   in
   let hdS1 =
     real_lt_trans (real_const (b5dQ_delta0 q epsQ))
       (real_const
         (b5dQ_lbSdiff_val q
           (coq_Qmult
             (coq_Qdiv epsQ
               (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                 Coq_xH } q))
             (b5dQ_kS q))))
       _UU03b4_S1 hqS1 hlbS1
   in
   let hqS2 =
     real_const_lt (b5dQ_delta0 q epsQ)
       (b5dQ_lbSdiff_val q { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
   in
   let hlbS2 =
     b5dQ_p4g_leaf_S q x hxr { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
       nM
   in
   let hdS2 =
     real_lt_trans (real_const (b5dQ_delta0 q epsQ))
       (real_const
         (b5dQ_lbSdiff_val q { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }))
       _UU03b4_S2 hqS2 hlbS2
   in
   b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
     (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2) (real_const tau)
     (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ))
       (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2
       (b5dQ_min_lb (real_const (b5dQ_delta0 q epsQ)) _UU03b4_E _UU03b4_S1
         hdE hdS1)
       hdS2)
     (real_const_lt (b5dQ_delta0 q epsQ) tau)))))))

(** val b5dQ_Hstep :
    coq_Q -> coq_Q -> nat -> nat -> (nat -> coq_QleT') -> nat -> nat ->
    cw_unit -> cw_unit -> real_le **)

let b5dQ_Hstep q epsQ m k hxr nA nM hk hk1 =
  let vapp = b5dQ_p4g_J_tail_lb_var q epsQ m k hxr nA nM in
  let Coq_existT (x, a) = vapp in
  let Coq_pair (_, a0) = a in
  let Coq_pair (r, r0) = a0 in
  let h_UU03b7_c = real_const_lt (b5dL_qdiv q m) (b5dQ_delta0 q epsQ) in
  let h_UU03b7_d =
    real_lt_trans (real_const (b5dL_qdiv q m))
      (real_const (b5dQ_delta0 q epsQ)) x h_UU03b7_c r0
  in
  let heta =
    real_eq_trans (real_abs (real_const (b5dL_qdiv q m)))
      (real_const (coq_Qabs (b5dL_qdiv q m))) (real_const (b5dL_qdiv q m))
      (b5dL_abs_const (b5dL_qdiv q m))
      (b5dH_real_const_qeq (coq_Qabs (b5dL_qdiv q m)) (b5dL_qdiv q m))
  in
  let h_UU03b7_abs =
    RealSetoid.real_lt_compat (real_const (b5dL_qdiv q m))
      (real_abs (real_const (b5dL_qdiv q m))) x x
      (real_eq_sym (real_abs (real_const (b5dL_qdiv q m)))
        (real_const (b5dL_qdiv q m)) heta)
      (real_eq_refl x) h_UU03b7_d
  in
  let hxh = b5dQ_xph_unit q m k in
  let heps1pos =
    real_const_pos (b5dL_epsQ1 m epsQ)
      (coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
        (b5dL_epsQ1 m epsQ))
  in
  let hcore =
    r (real_const (b5dL_qdiv q m)) h_UU03b7_abs hxh
      (real_const (b5dL_epsQ1 m epsQ)) heps1pos
  in
  let hstepR =
    b5dQ_step_inst q m k hxr hk1 hk hxh
      (real_plus
        (real_mult
          (real_const
            (coq_Qdiv epsQ
              (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
                Coq_xH } q)))
          (real_abs (real_const (b5dL_qdiv q m))))
        (real_const (b5dL_epsQ1 m epsQ)))
      hcore
  in
  RealSetoid.real_le_id_r
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q m k)) hk))))
    (real_plus
      (real_mult
        (real_const
          (coq_Qdiv epsQ
            (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden =
              Coq_xH } q)))
        (real_abs (real_const (b5dL_qdiv q m))))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_const (b5dL_bk q m epsQ k)) (b5dQ_rhs_bk q m k epsQ) hstepR

(** val b5dQ_Hmod :
    coq_Q -> coq_Q -> (nat, (coq_NatLe, nat -> __ -> cw_unit -> cw_unit ->
    real_le) coq_And) sigT **)

let b5dQ_Hmod q epsQ =
  let s = q_arch_inv (coq_Qdiv (b5dQ_delta0 q epsQ) q) in
  let Coq_existT (x, _) = s in
  let m = add x (S (S O)) in
  Coq_existT (m, (Coq_pair ((coq_NatLe_lift (S O) m), (fun k _ ->
  match k with
  | O ->
    let s0 = b5dQ_S_lb_tail_k0 q m in
    let Coq_existT (x0, _) = s0 in
    let s1 = b5dQ_S_ub_tail_k0 q m in
    (fun hk hk1 ->
    let Coq_existT (x1, _) = s1 in
    b5dQ_Hstep q epsQ m O (b5dQ_tkq_Hxr q m O) x0 x1 hk hk1)
  | S n ->
    let s0 = b5dQ_S_lb_tail_kS q m (S n) in
    let Coq_existT (x0, _) = s0 in
    let s1 = b5dQ_S_ub_tail_kS q m (S n) in
    (fun hk hk1 ->
    let Coq_existT (x1, _) = s1 in
    b5dQ_Hstep q epsQ m (S n) (b5dQ_tkq_Hxr q m (S n)) x0 x1 hk hk1)))))

(** val b5dQ_E_rational_zero : coq_Q -> cw_unit -> real_eq **)

let b5dQ_E_rational_zero q hq =
  b5dL_E_rational_zero_premise q (fun x _ -> b5dQ_Hmod q x) hq

(** val b5dS_E_pair_close :
    coq_Q -> (nat, (coq_Q, (coq_QltT, __) coq_And) sigT) sigT **)

let b5dS_E_pair_close eps =
  let Coq_existT (x, _) = b5b_arch2 in
  let s =
    q_arch_inv
      (coq_Qdiv eps
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO (Coq_xO (Coq_xI Coq_xH))));
          coq_Qden = Coq_xH } x))
  in
  let Coq_existT (x0, _) = s in
  let k =
    coq_Qplus
      (coq_Qmult
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH } x)
        { coq_Qnum = (Z.of_nat (S x0)); coq_Qden = Coq_xH })
      (coq_Qplus
        (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH } x)
        { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH })
  in
  let x1 =
    coq_Qdiv
      (coq_Qmult { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH }
        (coq_Qdiv eps { coq_Qnum = (Zpos (Coq_xI Coq_xH)); coq_Qden =
          Coq_xH }))
      k
  in
  Coq_existT (x0, (Coq_existT (x1, (Coq_pair
  ((coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH } x1), __)))))

(** val b5dS_E_zero_on_unit :
    coq_Real -> cw_unit -> real_lt -> real_lt -> real_eq **)

let b5dS_E_zero_on_unit x hx hx0 hx1 epsQ _ =
  let hhalfT =
    coq_Qlt_to_QltT { coq_Qnum = Z0; coq_Qden = Coq_xH }
      (coq_Qdiv epsQ { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
  in
  let s =
    b5dS_E_pair_close
      (coq_Qdiv epsQ { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
  in
  let Coq_existT (x0, s0) = s in
  let Coq_existT (x1, a) = s0 in
  let Coq_pair (q, _) = a in
  let Coq_existT (_, a0) = hx0 in
  let Coq_pair (_, s1) = a0 in
  let Coq_existT (x2, _) = s1 in
  let Coq_existT (_, a1) = hx1 in
  let Coq_pair (_, s2) = a1 in
  let Coq_existT (x3, _) = s2 in
  let s3 = projT2 x x1 q in
  let Coq_existT (x4, _) = s3 in
  let nq = PeanoNat.Nat.max (PeanoNat.Nat.max x2 x3) x4 in
  let q0 = projT1 x nq in
  let hq = b5c_const_unit q0 in
  let s4 =
    b5dQ_E_rational_zero q0 hq
      (coq_Qdiv epsQ { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      hhalfT
  in
  let Coq_existT (x5, _) = s4 in
  Coq_existT ((PeanoNat.Nat.max (PeanoNat.Nat.max x0 nq) x5), (fun n _ ->
  coq_Qlt_to_QltT
    (coq_Qabs (coq_Qminus (projT1 (real_E x hx) n) (projT1 real_zero n))) epsQ))

(** val pi_triangle_direct_edge : real_eq **)

let pi_triangle_direct_edge =
  real_eq_trans cos_pi_half
    (real_mult cauchy_real_pi_leibniz
      (real_const
        (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
          { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
    (real_mult
      (real_const { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })
      arctan_one_real)
    (real_eq_sym
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (coq_Qdiv { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
            { coq_Qnum = (Zpos (Coq_xO Coq_xH)); coq_Qden = Coq_xH })))
      cos_pi_half
      (channel_w_eq_cos_pi_half a3_h4_value_bridge
        (b5b_hsc_theorem b5dS_E_zero_on_unit)))
    (channel_w_eq_two_theta a3_h4_value_bridge)
