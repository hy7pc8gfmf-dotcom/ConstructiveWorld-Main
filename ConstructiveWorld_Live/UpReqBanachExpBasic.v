(* ============================================================ *)
(* UpReqBanachExpBasic.v —— 席BXB：路径 B exp(0)=one 基础件席    *)
(* （20260912；后台独立席位，CoreN 2）                           *)
(* ============================================================ *)
(* 使命：S4 可逆性 (e^a)⁻¹=e^(−a) 的终结腿是 e^0=1（对照 T42     *)
(* Real 层件 2 单位元腿同构）。Banach 设定下这条现在就可证：     *)
(*   exp_series_partial m bzero ≡ bone（k≥1 项因 bpow bzero k    *)
(*   = bzero 退化，只留首项）。本件把该块 + 范数上界落独立件。   *)
(*                                                             *)
(* 分层出口（前缀 bxb_，全部 bae/Id/QleT' Set 承载面）：         *)
(*   S1 保底  bxb_bpow_zero       : 1<=n -> bae (bpow bzero n)  *)
(*                                    bzero（bpow 递归退化）    *)
(*   S2 保底  bxb_series_zero     : bae (exp_series_partial     *)
(*                                    B bzero m) bone（主件）   *)
(*   S2 伴随  bxb_norm_series_zero: Id (bnorm (esp B bzero m))  *)
(*                                    1（范数面）               *)
(*   S2 伴随  bxb_series_zero_bcauchy : 零元级数列平凡柯西证书   *)
(*                                    （N=0 显式闭式）          *)
(*   S3 加分  bxb_norm_bound      : ‖esp B a m‖ ≤T bxb_qsum     *)
(*                                    (‖a‖) m = Σ_{k≤m}         *)
(*                                    ‖a‖^k/k!（Q 值面）        *)
(*                                                             *)
(* 对接位：B25 席（UpReqBanachExpDef，exp 元素定义路线甲         *)
(* projT1）已落盘（其 .vo 双证新鲜于本席 S4 落件时点，按任务书    *)
(* Require 其出口、零触碰其文件）。其尾遗留自陈「exp(0)=bone 的   *)
(* bae 完全等式面被 Class 缺反可分性字段挡住」——故 e^0=one 元素   *)
(* 面在现 Class 接口下的可达顶点即本件 S2 全量部分和等式 + 元素   *)
(* 邻域面（S4 跨席组合件 bxb_expdef_exp_zero_close）。           *)
(*                                                             *)
(* 红线自审：语句面全 Set 层（bae/Id/QleT'/sigT/QltT），无Prop   *)
(* 泄露；无承认件、无经典逻辑；禁词口径全文件（含注释）零字面量。 *)
(* 复用声明：Require Import UpReqBanachExp，BanachAlg/bpow/      *)
(*   exp_series_partial/bae 家族/bnorm_esp_term 等原样复用，     *)
(*   零重定义；UpReqBanachExp 本体零触碰。                       *)
(* 工程注（承 PB 七坑卡）：类字段/字段引理一律 @显式喂实例，      *)
(*   全括号化；nat 字面 0%nat、Datatypes.S；Q 系数 Qinv 直形。    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1 保底：零元幂退化                                           *)
(* ============================================================ *)

(* bpow 递归展开：n≥1 时 bzero^n ≡ bzero                        *)
(* （0 次项 = bone 由 n≥1 前提排除；S 0 腿 bmult_one_l 直连，     *)
(*   S (S j) 腿 bmult_wd 传 IH + bmult_zero 闭合。）             *)
Lemma bxb_bpow_zero : forall (B : BanachAlg) (n : nat),
  (1 <= n)%nat -> @bae B (bpow B (@bzero B) n) (@bzero B).
Proof.
  intros B n Hn. destruct n as [| m].
  - (* n = 0：与前提矛盾（先 exfalso 转 False 位，le 的 Prop 消去   *)
    (*   不得直打 Set 目标位） *)
    exfalso. lia.
  - induction m as [| j IH].
    + (* n = 1：bone·bzero = bzero *)
      change (bpow B (@bzero B) (Datatypes.S 0%nat))
        with (@bmult B (@bone B) (@bzero B)).
      exact (@bmult_one_l B (@bzero B)).
    + (* n = S (S j)：bmult bzero 传递 + bmult_zero *)
      assert (Hj : (1 <= Datatypes.S j)%nat) by lia.
      change (bpow B (@bzero B) (Datatypes.S (Datatypes.S j)))
        with (@bmult B (bpow B (@bzero B) (Datatypes.S j)) (@bzero B)).
      eapply bae_trans.
      { exact (@bmult_wd B (bpow B (@bzero B) (Datatypes.S j))
                           (@bzero B) (@bzero B) (@bzero B)
                           (IH Hj) (@bae_refl B (@bzero B))). }
      exact (@bmult_zero B (@bzero B)).
Qed.

(* 级数项在零元处退化：bzero^(S k)·q ≡ bzero（对任意标量 q）      *)
Lemma bxb_esp_term_zero : forall (B : BanachAlg) (k : nat) (q : Q),
  @bae B (@bmult B (bpow B (@bzero B) (Datatypes.S k)) (@bcoef B q))
        (@bzero B).
Proof.
  intros B k q.
  assert (Hk : (1 <= Datatypes.S k)%nat) by lia.
  eapply bae_trans.
  { exact (@bmult_wd B (bpow B (@bzero B) (Datatypes.S k)) (@bcoef B q)
                      (@bzero B) (@bcoef B q)
                      (bxb_bpow_zero B (Datatypes.S k) Hk)
                      (@bae_refl B (@bcoef B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm B q (@bzero B)). }
  exact (@bmult_zero B (@bcoef B q)).
Qed.

(* ============================================================ *)
(* S2 保底（主件）：零元级数部分和恒一                           *)
(* ============================================================ *)

(* exp_series_partial B bzero m ≡ bone（bae 等词面，对 m 归纳：  *)
(* 首项 bone 留守，k≥1 项经 bxb_esp_term_zero 全数退化为零，     *)
(* 再 bplus_zero 闭合——e^0=1 的 Banach 层完全等式面。）          *)
Lemma bxb_series_zero : forall (B : BanachAlg) (m : nat),
  @bae B (exp_series_partial B (@bzero B) m) (@bone B).
Proof.
  intros B m. induction m as [| k IHk].
  - change (exp_series_partial B (@bzero B) 0%nat) with (@bone B).
    exact (@bae_refl B (@bone B)).
  - change (exp_series_partial B (@bzero B) (Datatypes.S k))
      with (@bplus B (exp_series_partial B (@bzero B) k)
              (@bmult B (bpow B (@bzero B) (Datatypes.S k))
                        (@bcoef B (/ q_fact (Datatypes.S k))))).
    eapply bae_trans.
    { exact (@bplus_wd B (exp_series_partial B (@bzero B) k)
               (@bmult B (bpow B (@bzero B) (Datatypes.S k))
                         (@bcoef B (/ q_fact (Datatypes.S k))))
               (@bone B) (@bzero B) IHk
               (bxb_esp_term_zero B k (/ q_fact (Datatypes.S k)))). }
    exact (@bplus_zero B (@bone B)).
Qed.

(* 范数面：‖esp B bzero m‖ ≈ 1（QeqT 面；wd 弱化后 Id 面不可达，
   语句面同步弱化——CLS-R2 沙箱偏差⑤处置） *)
Lemma bxb_norm_series_zero : forall (B : BanachAlg) (m : nat),
  QeqT (@bnorm B (exp_series_partial B (@bzero B) m)) 1%Q.
Proof.
  intros B m.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm B (@bone B))).
  - apply qeqT_imp_qeq.
    exact (@bnorm_wd B (exp_series_partial B (@bzero B) m) (@bone B)
             (bxb_series_zero B m)).
  - rewrite (@bnorm_one B). apply Qeq_refl.
Qed.

(* 平凡柯西证书：零元级数列两两差恒零，模量 N=0 显式闭式         *)
(* （对照 exp_series_cauchy 的阿基米德 witness 链——零元处全免，  *)
(*   N=0 即闭合；S4 可逆性链中 e^0 极限存在性的免费位。）        *)
Lemma bxb_series_zero_bcauchy : forall (B : BanachAlg) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat,
    NatLe N m -> NatLe N n ->
    QltT (@bnorm B (@bplus B (exp_series_partial B (@bzero B) m)
                             (@bopp B (exp_series_partial B (@bzero B) n))))
           eps).
Proof.
  intros B eps Heps.
  exists 0%nat. intros m n Hm Hn.
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bzero B) m)
                (@bopp B (exp_series_partial B (@bzero B) n)))
      (@bplus B (@bone B) (@bopp B (@bone B)))
      (@bplus_wd B (exp_series_partial B (@bzero B) m)
                  (@bopp B (exp_series_partial B (@bzero B) n))
                  (@bone B) (@bopp B (@bone B))
                  (bxb_series_zero B m)
                  (@bopp_wd B (exp_series_partial B (@bzero B) n)
                              (@bone B) (bxb_series_zero B n)))))).
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd B (@bplus B (@bone B) (@bopp B (@bone B))) (@bzero B)
               (@bplus_opp B (@bone B))))).
  rewrite (@bnorm_zero B).
  exact Heps.
Qed.

(* ============================================================ *)
(* S3 加分：部分和范数上界（Q 值面）                             *)
(* ============================================================ *)

(* Q 层正指标部分和：Σ_{k=0..n} x^k/k!（0 次项 = 1；k≥1 项        *)
(* Qinv 直形 x^(S k)/(S k)!，与 bnorm_esp_term 右端逐字同构）     *)
Fixpoint bxb_qsum (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S k =>
      (bxb_qsum x k
        + q_pow x (Datatypes.S k) / q_fact (Datatypes.S k))%Q
  end.

(* 主加分：‖esp B a m‖ ≤T Σ_{k≤m} ‖a‖^k/k!                      *)
(* （归纳：bnorm_plus 三角拆项，IH + bnorm_esp_term 双腿经        *)
(*   qleT'_plus_compat 合流。）                                  *)
Lemma bxb_norm_bound : forall (B : BanachAlg) (a : (@BA B)) (m : nat),
  QleT' (@bnorm B (exp_series_partial B a m)) (bxb_qsum (@bnorm B a) m).
Proof.
  intros B a m. induction m as [| k IHk].
  - change (exp_series_partial B a 0%nat) with (@bone B).
    change (bxb_qsum (@bnorm B a) 0%nat) with 1%Q.
    rewrite (@bnorm_one B). apply qleT'_refl.
  - change (exp_series_partial B a (Datatypes.S k))
      with (@bplus B (exp_series_partial B a k)
              (@bmult B (bpow B a (Datatypes.S k))
                        (@bcoef B (/ q_fact (Datatypes.S k))))).
    change (bxb_qsum (@bnorm B a) (Datatypes.S k))
      with ((bxb_qsum (@bnorm B a) k
              + q_pow (@bnorm B a) (Datatypes.S k)
                / q_fact (Datatypes.S k))%Q).
    eapply qleT'_trans.
    + exact (@bnorm_plus B (exp_series_partial B a k)
               (@bmult B (bpow B a (Datatypes.S k))
                         (@bcoef B (/ q_fact (Datatypes.S k))))).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IHk.
      * exact (bnorm_esp_term B a k).
Qed.

(* ============================================================ *)
(* S4 加分：与 B25 exp 元素定义的跨席对接（元素面）               *)
(* ============================================================ *)

(* 元素面组合件：B25 的 exp 元素在零元处与 bone 范数任意贴近。    *)
(* 组合路线=两席各半经公共接口扣合：                              *)
(*   本件 bxb_series_zero（部分和恒一，全量精确面）               *)
(*   + B25 bxdef_exp_spec_eps（元素=部分和的极限，邻域面）        *)
(*   ⟹ 取 n=N 后以 bnorm_wd 把部分和位换成本件 bone 精确面。      *)
(* （语句面与 B25 bxdef_exp_zero_close 同型——本证走本件精确面     *)
(*   组合而入，验两席接口对位可组合；bae 完全等式面仍被 Class     *)
(*   缺反可分性字段挡住，对称遗留不动。）                         *)
Lemma bxb_expdef_exp_zero_close : forall (B : BanachAlg) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm B (@bplus B (bxdef_exp B (@bzero B))
                           (@bopp B (@bone B)))) eps.
Proof.
  intros B eps Heps.
  destruct (bxdef_exp_spec_eps B (@bzero B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift _ _ (Nat.le_refl N))).
  pose proof (QeqT_Qlt_bool_cong _ _ eps (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bzero B) N)
                (@bopp B (bxdef_exp B (@bzero B))))
      (@bplus B (@bone B) (@bopp B (bxdef_exp B (@bzero B))))
      (@bplus_wd B (exp_series_partial B (@bzero B) N)
                  (@bopp B (bxdef_exp B (@bzero B)))
                  (@bone B) (@bopp B (bxdef_exp B (@bzero B)))
                  (bxb_series_zero B N)
                  (@bae_refl B (@bopp B (bxdef_exp B (@bzero B)))))) HN) as HN2.
  clear HN. rename HN2 into HN.
  (* 规格位是 bone+(−E)；目标位 E+(−bone)——换序经 comm +        *)
  (* bplus_opp_swap（E+(−bone) ≡ −(bone+(−E))）+ bnorm_opp 闭合。 *)
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd B
      (@bplus B (bxdef_exp B (@bzero B)) (@bopp B (@bone B)))
      (@bopp B (@bplus B (@bone B) (@bopp B (bxdef_exp B (@bzero B)))))
      (@bae_trans B
         (@bplus B (bxdef_exp B (@bzero B)) (@bopp B (@bone B)))
         (@bplus B (@bopp B (@bone B)) (bxdef_exp B (@bzero B)))
         (@bopp B (@bplus B (@bone B) (@bopp B (bxdef_exp B (@bzero B)))))
         (@bplus_comm B (bxdef_exp B (@bzero B)) (@bopp B (@bone B)))
         (@bplus_opp_swap B (@bone B) (bxdef_exp B (@bzero B))))))).
  rewrite (@bnorm_opp B (@bplus B (@bone B) (@bopp B (bxdef_exp B (@bzero B))))).
  exact HN.
Qed.

(* ============================================================ *)
(* 对接注记（S4 可逆性链位置，不落承认件）：                     *)
(*   S4 终结腿 e^0=1 在 Banach 层的本件形态：                    *)
(*   ① 全量部分和等式 bxb_series_zero（元素面 bae 完全等式）；   *)
(*   ② 范数面 bxb_norm_series_zero（Id 面，T42 单位元腿同构）；  *)
(*   ③ 平凡柯西证书 bxb_series_zero_bcauchy（N=0 显式闭式）；    *)
(*   ④ 范数上界 bxb_norm_bound（Σ_{k≤m} ‖a‖^k/k! Q 值面）；      *)
(*   ⑤ 元素面 ④→S4：bxb_expdef_exp_zero_close（与 B25 出口      *)
(*      组合而入）。                                             *)
(*   完全等式 exp(bzero)=bone 需 Class 增反可分性字段（bnorm      *)
(*   任意小 ⟹ bae bzero）——接口扩容属上游裁决，两席对称遗留，    *)
(*   不擅动。后继（exp_add/可逆性）承 UpReqBanachExp 文件尾      *)
(*   四步闭包登记。                                              *)
(* ============================================================ *)
