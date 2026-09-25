(* ============================================================ *)
(*   位1 UpReqDist.v:3091 transition_normalization（ReqSteadyState req 层）   *)
(*        → 两点世界行归一核 supply（half+half==one 纯接口代数链；            *)
(*          Token/vocab 世界专属非同语句，本件改走实例供给路线落地）           *)
(*   位2 UpReqDist.v:3096 detailed_balance（ReqSteadyState req 层）           *)
(*        → 源核缩放族 t(s,s')=p(s')·c supply（assoc-comm 纯代数；非循环——    *)
(*          普查依据 G13:120/:528 消费节内 Variable 本体，禁直喂已定谳）       *)
(* 消融形（诚实申报）：全参 {R}{RIS} 抽象载体，零桥零具体实例零数据槽隐藏；    *)
(*   逐点代数不依赖载体大小，两点供给世界为最小可达面。                       *)
(* 分级：位1 = N3（实例供给）；位2 = N3（实例供给·核族构造）。                *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpReqDist。          *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

Section UabT13cDist.

Context {R0 : Set} {RIS0 : RealInterfaceEnhancedSetoid R0}.

Definition uab_t2sum (f : bool -> R0) : R0 := plus (f true) (f false).

Definition uab_half : R0 :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* ---- 交换核族引理：p(s)·(p(s')·c) == p(s')·(p(s)·c) ---- *)
Lemma uabT13c_swap_req_gen :
  forall (p : bool -> R0) (c : R0) (s s' : bool),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   (mult_assoc (p s) (p s') c)
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                                               (mult_comm (p s) (p s')) (req_refl c))
                              (req_sym (mult (p s') (mult (p s) c))
                                       (mult (mult (p s') (p s)) c)
                                       (mult_assoc (p s') (p s) c)))).
Qed.

(* ---- 两点行归一代数核：half+half == one ---- *)
Lemma uabT13c_half_row : req (plus uab_half uab_half) one.
Proof.
  unfold uab_half.
  assert (H1 : req (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                   (inv_pos (plus one one) (plus_positive one one one_pos one_pos))).
  { exact (req_trans (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)
                     (inv_pos (plus one one) (plus_positive one one one_pos one_pos))
                     (mult_comm one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult_one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))). }
  assert (HDL : req (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                    (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                          (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))).
  { exact (req_trans (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                     (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                     (mult_comm (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (req_trans (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                                (plus (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one))
                                (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                (distrib (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one one)
                                (req_plus_compat (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)))). }
  exact (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) one
                   (req_trans (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                              (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                              (req_plus_compat (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1)
                                               (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1))
                              (req_sym (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                       (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                       HDL))
                   (inv_pos_correct (plus one one) (plus_positive one one one_pos one_pos))).
Qed.

(* ---- 位1 ←UpReqDist:3091（行归一 discharge：两点一致核） ---- *)
Theorem uabT13c_dist_norm3091 :
  forall s : bool,
    req (uab_t2sum (fun s' : bool => uab_half)) one.
Proof.
  intro s.
  unfold uab_t2sum.
  exact uabT13c_half_row.
Qed.

(* ---- 位2 ←UpReqDist:3096（详细平衡 discharge：源核缩放族 t(s,s')=p(s')·c；
        p 取 reqd_boltzmann_prob 实形（base_loss/D/Z 全参自由）） ---- *)
Theorem uabT13c_dist_db3096 :
  forall (base_loss : bool -> R0) (D : R0) (D_pos : lt zero D)
         (Z : R0) (Z_pos : lt zero Z) (c : R0),
    forall s s' : bool,
      req (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s')
                (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s) c))
          (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s)
                (mult (@reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos s') c)).
Proof.
  intros base_loss D D_pos Z Z_pos c s s'.
  exact (uabT13c_swap_req_gen
           (fun x : bool => @reqd_boltzmann_prob R0 RIS0 bool base_loss D D_pos Z Z_pos x)
           c s' s).
Qed.

End UabT13cDist.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13c_dist_norm3091.
Print Assumptions uabT13c_dist_db3096.
