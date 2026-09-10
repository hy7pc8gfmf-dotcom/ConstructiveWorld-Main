(* ============================================================ *)
(* UpReqLogPrimD.v —— 槽放电战役 G5：log/exp 基元放电器（C 档 26 族/43 槽） *)
(*   广义旗舰链 G5 执行席，2026-09-10                              *)
(* ------------------------------------------------------------------ *)
(* 引擎坐标实读（普查 G5 节 + §四落点纪律执行记录）：                  *)
(*   ① 接口字段（CW219 L40464 起 RealInterfaceEnhancedSetoid，req 版）：*)
(*    log/log_inv 带正性参；log_mult/log_one/log_inv_log/exp_neg_log_inv *)
(*    req 形在盘；log_le_linear_eps 仅逐 eps 形（E152-5 先例）。        *)
(*    接口无 log 相容字段、无 log_inv∘exp_neg 字段、无 exp_neg 外延字段。*)
(*   ② 根基元（CW219 具体 Real 层，锚点法已证，本席 sed 实读）：        *)
(*    real_log_exp_neg@42231（log(e^{-x})==-x）/ real_log_wd@42277      *)
(*    （log 参数 real_eq 兼容）/ real_log_proof_irrel@42291（见证无关） *)
(*    / real_log_le_mono@112106（log 单调 le 版）/ real_log_mult@40403  *)
(*    / real_log_one@40413 / real_log_inv_log@40424 /                   *)
(*    real_exp_neg_log_inv@40431。                                      *)
(*   ③ 桥核对（红线判词）：req→le 单向升格由接口字段 lt_le_iff 右支     *)
(*    自带（本席新发现基元 logd_req_to_le——req 层无条件）；le/lt→       *)
(*    real_le_b 单向（UpRealLeB real_le_to_le_b@78）；逆向 Or 形精确    *)
(*    收口构造性不可证（UpRealLeB 尾注台账），故 log_le_linear/log_eq_  *)
(*    linear 等号槽（S 档 G6 属）不属本席、本席亦不触逆向桥。           *)
(* ------------------------------------------------------------------ *)
(* G5 归约格（泛型 RIS 接口层，全部 Set 层语句零 Prop 泄露）：           *)
(*   [P0] logd_req_to_le           —— req⟹le（lt_le_iff inr，无条件）  *)
(*   [P0] logd_req_opp_opp / logd_req_plus_zero_l / logd_req_plus_zero_r *)
(*        —— req 代数小件（opp 对合 / 加法零消去，接口字段纯推导）      *)
(*   [P1] logd_exp_neg_ext         —— req x y ⟹ req (exp_neg x) (exp_neg y) *)
(*        【接口层无条件真定理】＝放电 req_exp_neg_ext@UpSigMigrate:521  *)
(*        （P0 升 le 双向 + exp_neg_le_decr + le_antisym 收口）          *)
(*   [P1] logd_lt_req_transport / logd_pos_of_agree —— 正性运输：        *)
(*        放电 expf_pos@UpReqFEPAttn:264（条件放电，供给槽=expf_agree）  *)
(*   [P2] logd_log_compat_of_mono  —— compat ⟸ log 单调 le 单槽         *)
(*        （UpReqU2 log_req_compat 同位先例，logd_ 独立重建）            *)
(*   [P2] logd_log_inv_one_inv_of_compat —— inv_one_inv ⟸ compat 槽     *)
(*        （log_mult 分解 + compat 运输至 log one + 零消去）             *)
(*   [P2] logd_log_inv_exp_neg_of_log_exp_neg / logd_log_exp_neg_of_     *)
(*        log_inv_exp_neg —— {log∘exp_neg, log_inv∘exp_neg} 双向互归约  *)
(*        （log_inv_log + opp 对合；对内互推，对外需一根基元供给）       *)
(* ------------------------------------------------------------------ *)
(* Real 层无条件闭合（T2 模板②，槽形语句；CW219 根基元直喂）：          *)
(*   [B1] logd_log_compat_real（双形 a=mono 链 / b=real_log_wd 直喂）    *)
(*        放电族：log_req_compat(9)/b_log_compat/req_log_compat/         *)
(*        req_log_compat_slot/ralt_log_req_compat/rdl_log_req_compat/    *)
(*        rppo_log_req_compat = 15 槽                                   *)
(*   [B2] logd_log_exp_neg_real（real_log_exp_neg 逐字同形直喂）         *)
(*        放电族：log_exp_neg(2)/dist_log_exp_neg(2)/b_log_exp_neg/      *)
(*        req_log_exp_neg = 6 槽                                        *)
(*   [B3] logd_log_inv_one_inv_real（P2 组装 B1）                        *)
(*        放电族：log_inv_one_inv(2)/dist_log_inv_one_inv(3) = 5 槽      *)
(*   [B4] logd_log_inv_exp_neg_real（P2 组装 B2）                        *)
(*        放电族：log_inv_exp_neg_req(5)/ralt_log_inv_exp_neg_req/       *)
(*        rdl_log_inv_exp_neg_req = 7 槽                                *)
(*   [B5] logd_log_witness_real（log 见证无关 req 形；real_log_proof_    *)
(*        irrel 的 req 槽形双形）；[B6] logd_exp_neg_ext_real（P1 实例化）*)
(* ------------------------------------------------------------------ *)
(* 判词表（43 槽全清偿分类；35 放电 / 7 S 阻塞 / 1 N）：                 *)
(*   放电 35 槽 = B1(15)+B2(6)+B3(5)+B4(7)+expf_pos(1)+req_exp_neg_ext(1) *)
(*   S 阻塞 7 槽（复合恒等式/微分记录，基元供给链已明，超本席时间盒）：  *)
(*    - energy_in_log_boltzmann_bridge@UpSigMigrate:65 /                 *)
(*      free_energy_boltzmann_bridge@UpSigMigrate:70：FEP 复合恒等式，    *)
(*      供给=partition_condition(N 参)+B1+B2+sum 代数；复合重建另席。    *)
(*    - rdf_log_diff@UpReqRDF:1704：reqRDF 微分记录（rdf_df+eps-delta）， *)
(*      接口无 log 导数字段；需 log 导数 req 化+复合链微分引擎。         *)
(*    - real_kl_decomp_full@UpRealLeB:218：FEP 分解 Real 层复合          *)
(*      （F==F(boltzmann)+D·Σ kl_term）；供给=B2+kl_log_inv 先例+sum 代数。*)
(*    - req_entropy_temp_explicit@UpFirewallReq:122 /                    *)
(*      req_relative_entropy_temp_decomp@128 / req_temp_strict_ident2@144：*)
(*      热力学/KL 温度分解复合；供给=B1+B2+sumf 代数，复合重建另席。     *)
(*   N 1 槽：expf_agree@UpReqFEPAttn:265 —— expf 抽象算子的规格本身，    *)
(*    不可放电；收窄路线=以 exp_pos_fn_setoid 直替换 expf（签名变化）。  *)
(* 防撞：logd_ 前缀全库 grep 实测零命中（hzlogd_/gibbsd_ 异前缀在案）。  *)
(* 双形并存：B1 双形（mono 链/real_log_wd 直喂）；B3 与 UpStepKL         *)
(*   kl_log_inv@574 同形（cw_log 形先例，本件 req 槽形独立组装）；       *)
(*   P2 compat 归约与 UpReqU2 log_req_compat 同位（logd_ 独立版）。      *)
(* 红线：Set 层零 Prop（结论全 req/lt/le 接口 Set 值）；全 Qed 闭合；    *)
(*   零公理；既有文件零改；零 git；温控 guard 错峰（_logd_g2.ps1）。     *)
(* 编译配方：_logd_g2.ps1 温控包装                                       *)
(*   coqc -Q . "" -Q "..\001" "" UpReqLogPrimD.v（单核绑核，零裸调）     *)
(* G4：coqchk -Q . "" -Q "..\001" "" UpReqLogPrimD（长窗，禁 -o）        *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Part 0：req 代数小件（接口字段纯推导，零 destruct）                 *)
(* ============================================================ *)

(* P0-a：req ⟹ le（lt_le_iff 右支；req 层单向升格基元，本席新发现——
   与 real_le→real_le_b 同为单向，逆向 Or 收口不可证不动） *)
Lemma logd_req_to_le : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (x y : R), req x y -> le x y.
Proof.
  intros R RIS x y H.
  exact (lt_le_iff x y (inr H)).
Qed.

(* P0-b：加法左零（zero + a ≡ a；plus_zero 右零形经 comm 换位） *)
Lemma logd_req_plus_zero_l : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (a : R), req (plus zero a) a.
Proof.
  intros R RIS a.
  apply (req_trans (plus zero a) (plus a zero) a).
  - exact (plus_comm zero a).
  - exact (plus_zero a).
Qed.

(* P0-c：opp 对合（opp (opp a) ≡ a；plus_opp 双例 + assoc/comm/zero 链） *)
Lemma logd_req_opp_opp : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (a : R), req (opp (opp a)) a.
Proof.
  intros R RIS a.
  assert (H1 : req (plus (opp a) (opp (opp a))) zero) by exact (plus_opp (opp a)).
  assert (H2 : req (plus a (opp a)) zero) by exact (plus_opp a).
  apply (req_trans (opp (opp a)) (plus zero (opp (opp a))) a).
  - apply req_sym. exact (logd_req_plus_zero_l R RIS (opp (opp a))).
  - apply (req_trans (plus zero (opp (opp a)))
                     (plus (plus a (opp a)) (opp (opp a))) a).
    + apply (req_plus_compat zero (plus a (opp a)) (opp (opp a)) (opp (opp a))).
      * apply req_sym. exact H2.
      * apply req_refl.
    + apply (req_trans (plus (plus a (opp a)) (opp (opp a)))
                       (plus a (plus (opp a) (opp (opp a)))) a).
      * apply req_sym. exact (plus_assoc a (opp a) (opp (opp a))).
      * apply (req_trans (plus a (plus (opp a) (opp (opp a))))
                         (plus a zero) a).
        -- apply (req_plus_compat a a (plus (opp a) (opp (opp a))) zero
                    (req_refl a) H1).
        -- exact (plus_zero a).
Qed.

(* P0-d：加法右零消去（a + b ≡ zero ⟹ b ≡ opp a） *)
Lemma logd_req_plus_zero_r : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (a b : R), req (plus a b) zero -> req b (opp a).
Proof.
  intros R RIS a b H.
  apply (req_trans b (plus zero b) (opp a)).
  - apply req_sym. exact (logd_req_plus_zero_l R RIS b).
  - apply (req_trans (plus zero b) (plus (plus (opp a) a) b) (opp a)).
    + apply (req_plus_compat zero (plus (opp a) a) b b).
      * apply req_sym.
        apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
        -- exact (plus_comm (opp a) a).
        -- exact (plus_opp a).
      * apply req_refl.
    + apply (req_trans (plus (plus (opp a) a) b)
                       (plus (opp a) (plus a b)) (opp a)).
      * apply req_sym. exact (plus_assoc (opp a) a b).
      * apply (req_trans (plus (opp a) (plus a b))
                         (plus (opp a) zero) (opp a)).
        -- apply (req_plus_compat (opp a) (opp a) (plus a b) zero
                    (req_refl (opp a)) H).
        -- exact (plus_zero (opp a)).
Qed.

(* ============================================================ *)
(* Part 1：接口层基元（泛型 RIS；条件形供给槽显式位）                    *)
(* ============================================================ *)

(* P1-a：exp_neg 对 req 兼容——接口层无条件真定理（放电
   req_exp_neg_ext@UpSigMigrate:521 整族）。
   路线：req 经 lt_le_iff 右支升 le 双向，exp_neg_le_decr 反向各得一支，
   le_antisym 收口。全接口字段，零额外供给。 *)
Lemma logd_exp_neg_ext : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (x y : R), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros R RIS x y Hxy.
  apply (le_antisym (exp_neg x) (exp_neg y)).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le R RIS y x).
    exact (req_sym x y Hxy).
  - apply exp_neg_le_decr.
    apply (logd_req_to_le R RIS x y).
    exact Hxy.
Qed.

(* P1-b：lt 正性沿 req 运输（req_lt_compat 零点特化） *)
Lemma logd_lt_req_transport : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (a b : R), req a b -> lt zero a -> lt zero b.
Proof.
  intros R RIS a b H Hlt.
  exact (req_lt_compat zero zero a b (req_refl zero) H Hlt).
Qed.

(* P1-c：逐点正性运输（放电 expf_pos@UpReqFEPAttn:264——条件放电，
   供给槽 = expf_agree（req (expf x) (exp_pos_fn_setoid x)）+
   exp_pos_fn_setoid 正性（exp_neg 族字段直推）。expf_agree 本身 =
   expf 抽象算子的规格（N 槽，不可放电），见判词表。） *)
Lemma logd_pos_of_agree : forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
    (ef tgt : R -> R),
  (forall x : R, req (ef x) (tgt x)) ->
  (forall x : R, lt zero (tgt x)) ->
  forall x : R, lt zero (ef x).
Proof.
  intros R RIS ef tgt Hagree Hpos x.
  apply (logd_lt_req_transport R RIS (tgt x) (ef x)).
  - apply req_sym. exact (Hagree x).
  - exact (Hpos x).
Qed.

(* P2-a：log 相容 ⟸ log 单调 le 单槽（UpReqU2 log_req_compat 同位先例，
   logd_ 独立重建；req 升 le 双向 + le_antisym 收口） *)
Lemma logd_log_compat_of_mono :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    le x y -> le (log x Hx) (log y Hy)) ->
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros R RIS Hmono x y Hx Hy Hxy.
  apply (le_antisym (log x Hx) (log y Hy)).
  - apply (Hmono x y Hx Hy).
    exact (lt_le_iff x y (inr Hxy)).
  - apply (Hmono y x Hy Hx).
    exact (lt_le_iff y x (inr (req_sym x y Hxy))).
Qed.

(* P2-b：log(1/x) ≡ −log x ⟸ log 相容槽（log_mult 分解 + 相容运输至
   log one + 加法零消去；UpReqFEPAttn/UpReqDist 同名槽的归约件） *)
Lemma logd_log_inv_one_inv_of_compat :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
  (forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy)) ->
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros R RIS Hcompat x Hx Hi.
  assert (Hponelt : lt zero one) by exact one_pos.
  assert (Hprod : req (mult (inv_pos x Hx) x) one).
  { apply (req_trans (mult (inv_pos x Hx) x) (mult x (inv_pos x Hx)) one).
    - exact (mult_comm (inv_pos x Hx) x).
    - exact (inv_pos_correct x Hx). }
  assert (Hlog1 : req (log (mult (inv_pos x Hx) x)
                         (mult_positive (inv_pos x Hx) x Hi Hx)) zero).
  { apply (req_trans (log (mult (inv_pos x Hx) x)
                       (mult_positive (inv_pos x Hx) x Hi Hx))
                     (log one one_pos) zero).
    - exact (Hcompat (mult (inv_pos x Hx) x) one
               (mult_positive (inv_pos x Hx) x Hi Hx) one_pos Hprod).
    - exact (log_one one_pos). }
  assert (Hdec : req (plus (log (inv_pos x Hx) Hi) (log x Hx)) zero).
  { exact (req_trans (plus (log (inv_pos x Hx) Hi) (log x Hx))
                     (log (mult (inv_pos x Hx) x)
                        (mult_positive (inv_pos x Hx) x Hi Hx)) zero
                     (req_sym (log (mult (inv_pos x Hx) x)
                            (mult_positive (inv_pos x Hx) x Hi Hx))
                        (plus (log (inv_pos x Hx) Hi) (log x Hx))
                        (log_mult (inv_pos x Hx) x Hi Hx))
                     Hlog1). }
  apply (req_sym (opp (log x Hx)) (log (inv_pos x Hx) Hi)).
  apply (req_trans (opp (log x Hx)) (opp (opp (log (inv_pos x Hx) Hi)))
                   (log (inv_pos x Hx) Hi)).
  - apply req_sym.
    apply req_opp_compat.
    apply req_sym.
    exact (logd_req_plus_zero_r R RIS (log (inv_pos x Hx) Hi) (log x Hx) Hdec).
  - exact (logd_req_opp_opp R RIS (log (inv_pos x Hx) Hi)).
Qed.

(* P2-c：log_inv∘exp_neg ≡ id ⟸ log∘exp_neg ≡ −id 槽
   （log_inv_log 换形 + opp 对合；对内互归约之正向） *)
Lemma logd_log_inv_exp_neg_of_log_exp_neg :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
  (forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u)) ->
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intros R RIS Hlen x.
  apply (req_trans (log_inv (exp_neg x) (exp_neg_pos x))
                   (opp (log (exp_neg x) (exp_neg_pos x))) x).
  - exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - apply (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                     (opp (opp x)) x).
    + apply req_opp_compat. exact (Hlen x).
    + exact (logd_req_opp_opp R RIS x).
Qed.

(* P2-d：log∘exp_neg ≡ −id ⟸ log_inv∘exp_neg ≡ id 槽（P2-c 逆向对称；
   二槽对内互推，对外任一为根供给——Real 层根 = real_log_exp_neg@42231） *)
Lemma logd_log_exp_neg_of_log_inv_exp_neg :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R),
  (forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x) ->
  forall x : R, req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intros R RIS Hinv x.
  apply (req_sym (opp x) (log (exp_neg x) (exp_neg_pos x))).
  apply (req_trans (opp x) (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (log (exp_neg x) (exp_neg_pos x))).
  - apply req_opp_compat.
    apply (req_trans x (log_inv (exp_neg x) (exp_neg_pos x))
                      (opp (log (exp_neg x) (exp_neg_pos x)))).
    + apply req_sym. exact (Hinv x).
    + exact (log_inv_log (exp_neg x) (exp_neg_pos x)).
  - exact (logd_req_opp_opp R RIS (log (exp_neg x) (exp_neg_pos x))).
Qed.

(* ============================================================ *)
(* Part 2：Real 层无条件闭合（T2 模板②槽形；CW219 根基元直喂）           *)
(* ============================================================ *)

(* B1-a：log 参数 req 兼容（mono 链形：real_log_le_mono@CW219:112106 直喂
   P2-a；放电族 log_req_compat 等 15 槽） *)
Lemma logd_log_compat_real : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (logd_log_compat_of_mono Real RealEnhancedReal
           (fun (a b : Real) (Ha : lt zero a) (Hb : lt zero b)
              (Hab : le a b) => real_log_le_mono a b Ha Hb Hab)).
  exact Hxy.
Qed.

(* B1-b：同语句双形（real_log_wd@CW219:42277 直喂；殊途同归，双形并存） *)
Lemma logd_log_compat_real_wd : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  exact (real_log_wd x y Hx Hy Hxy).
Qed.

(* B2：log(e^{-x}) ≡ −x（real_log_exp_neg@CW219:42231 逐字同形直喂；
   放电族 log_exp_neg/dist_log_exp_neg/b_log_exp_neg/req_log_exp_neg
   = 6 槽；Real 层根供给，P2-c/d 之对外根） *)
Lemma logd_log_exp_neg_real : forall (x : Real),
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (real_log_exp_neg x).
Qed.

(* B3：log(1/x) ≡ −log x（P2-b 组装 B1；放电族 log_inv_one_inv(2)/
   dist_log_inv_one_inv(3) = 5 槽；UpStepKL kl_log_inv@574 cw_log 形
   同形先例，本件 req 槽形独立组装） *)
Lemma logd_log_inv_one_inv_real : forall (x : Real) (Hx : lt zero x)
    (Hi : lt zero (inv_pos x Hx)),
  req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Proof.
  intros x Hx Hi.
  exact (logd_log_inv_one_inv_of_compat Real RealEnhancedReal
           logd_log_compat_real x Hx Hi).
Qed.

(* B4：log_inv(e^{-x}) ≡ x（P2-c 组装 B2；放电族 log_inv_exp_neg_req(5)/
   ralt_log_inv_exp_neg_req/rdl_log_inv_exp_neg_req = 7 槽） *)
Lemma logd_log_inv_exp_neg_real : forall (x : Real),
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  apply (logd_log_inv_exp_neg_of_log_exp_neg Real RealEnhancedReal).
  intro u.
  exact (logd_log_exp_neg_real u).
Qed.

(* B5：log 见证无关（同点双正性见证换装 req 形；UpReqU2
   log_req_witness_compat 同位双形；Real 层根 = real_log_proof_irrel@42291） *)
Lemma logd_log_witness_real : forall (x : Real) (Hx Hx' : lt zero x),
  req (log x Hx) (log x Hx').
Proof.
  intros x Hx Hx'.
  exact (logd_log_compat_real x x Hx Hx' (req_refl x)).
Qed.

(* B6：exp_neg 外延 Real 实例化（P1-a 模板②特化，与 UpSigMigrate:521
   槽形逐位同形） *)
Lemma logd_exp_neg_ext_real : forall (x y : Real), req x y -> req (exp_neg x) (exp_neg y).
Proof.
  intros x y H.
  exact (logd_exp_neg_ext Real RealEnhancedReal x y H).
Qed.

(* ============================================================ *)
(* 闭合性审计（G3 关：全部主放电件 Print Assumptions）                   *)
(* ============================================================ *)
Print Assumptions logd_exp_neg_ext.
Print Assumptions logd_pos_of_agree.
Print Assumptions logd_log_compat_of_mono.
Print Assumptions logd_log_inv_one_inv_of_compat.
Print Assumptions logd_log_inv_exp_neg_of_log_exp_neg.
Print Assumptions logd_log_exp_neg_of_log_inv_exp_neg.
Print Assumptions logd_log_compat_real.
Print Assumptions logd_log_compat_real_wd.
Print Assumptions logd_log_exp_neg_real.
Print Assumptions logd_log_inv_one_inv_real.
Print Assumptions logd_log_inv_exp_neg_real.
Print Assumptions logd_log_witness_real.
Print Assumptions logd_exp_neg_ext_real.
