(* ============================================================ *)
(* UpReqBanachInvPre.v —— 席BINV2：路径 B S4 前移席（20260912） *)
(* ============================================================ *)
(* 使命：S4 可逆性终结腿 e^a·e^(−a)=e^0=1 的特例主链。          *)
(*   一般 bpow_add（二项式恒等）= 席 BA 领地，本席绕开；        *)
(*   本席攻其特例：x := a+(−a) 处处经 bplus_opp 塌缩为零，      *)
(*   (a+(−a))^n ≡ bzero（n≥1）不需要任何二项式系数层。          *)
(*                                                             *)
(* 分层出口（前缀 binv_，全 bae/Id Set 承载面）：               *)
(*   S1 保底  binv_bpow_opp_add   : 1<=n -> (a+(−a))^n ≡ bzero *)
(*             （n 归纳：首腿 plus_opp 消项，后续零元塌缩逐级） *)
(*   S1 咬合  binv_bpow_opp_add_mesh : 与 BXB bxb_bpow_zero     *)
(*             经 bpow_wd 传送对位（两席终点一致性证书）        *)
(*   S1 主锚  binv_esp_opp_add    : (a+(−a)) 级数部分和恒一     *)
(*             —— S4 终结腿 e^0=1 的全量部分和精确形态          *)
(*   S2 保底  binv_pair           : esp m a · esp m (−a) ≡      *)
(*             esp m (−a) + Σ_{k<m}(a^{S k}/(S k)!)·esp m (−a)  *)
(*             （柯西方块 esp_prod_square + 首行提出=配对余项； *)
(*               精确形式实测定形，见交付报告）                  *)
(*   S3 加分  对角线交错结构起步：                              *)
(*             binv_diag_term/binv_diag_term_pair +             *)
(*             逆元乘积四件 + 偶次塌缩种子 binv_bpow_opp2       *)
(*                                                             *)
(* 分工边界：一般 bpow_add = 席 BA 领地；本件只碰特例 x=a+(−a)。*)
(*   汇合点 = exp_add 总装席（下一批）：其取本件 S1 主锚为右侧  *)
(*   e^0 腿（部分和恒一，零极限免费），取 binv_pair 为左侧乘积  *)
(*   配对形，经三角转置（B3Sv2 批三）接通。                      *)
(*                                                             *)
(* 依赖复用（Require 原样复用，零重定义）：                      *)
(*   UpReqBanachExp  : BanachAlg 类/bpow/exp_series_partial/bae *)
(*                     家族/bplus_opp_swap/bnorm 族             *)
(*   UpReqBanachProd : bsum/和式引擎/bpow_comm_r/esp_as_bsum/   *)
(*                     esp_prod_square/bsum_rot                 *)
(*   UpReqBanachExpBasic : bxb_bpow_zero/bxb_series_zero        *)
(*                     （链终点咬合位）                          *)
(*                                                             *)
(* 红线自审：语句面全 Set 层（bae/Id/sigT/QltT），无命题层泄露  *)
(*   （证内 Prop 仅 Q 等式内衬，同库先例）；无承认件；无经典    *)
(*   逻辑；禁词口径全文件（含注释）零字面量。                    *)
(* 工程注（承 B3Sv2 七坑卡）：bae 无 rewrite 实例——change 定形  *)
(*   + bae_trans 显式中件链（中件一律显式 pin）；类字段/字段引理 *)
(*   一律 @显式喂实例全括号化；bmult_wd 实参序=源对(a,b)在前、   *)
(*   目标对(c,d)在后。nat 字面 0%nat、Datatypes.S。              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachExpBasic.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* §0 引擎补件（库内缺位的零元左消与 wd 传送）                   *)
(* ============================================================ *)

(* 左零消去：bzero·x ≡ bzero（类字段 bmult_zero 只给右零；       *)
(*   非交换类里经 bcoef 0 中转：bcoef_comm 换位 + bcoef_zero）。 *)
Lemma binv_bmult_zero_l : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B (@bzero B) x) (@bzero B).
Proof.
  intros B x.
  eapply bae_trans.
  - (* bzero·x ≡ (bcoef 0)·x *)
    apply (@bmult_wd B (@bzero B) x (@bcoef B 0%Q) x).
    + apply (@bae_sym B). exact (@bcoef_zero B).
    + apply (@bae_refl B).
  - (* (bcoef 0)·x ≡ x·(bcoef 0) ≡ x·bzero ≡ bzero *)
    apply (@bae_trans B _ (@bmult B x (@bcoef B 0%Q)) _).
    + apply (@bae_sym B). exact (@bcoef_comm B 0%Q x).
    + apply (@bae_trans B _ (@bmult B x (@bzero B)) _).
      * apply (@bmult_wd B x (@bcoef B 0%Q) x (@bzero B)).
        -- apply (@bae_refl B).
        -- exact (@bcoef_zero B).
      * exact (@bmult_zero B x).
Qed.

(* bpow 对 bae 的传送（归纳 + bmult_wd） *)
Lemma binv_bpow_wd : forall (B : BanachAlg) (x y : (@BA B)),
  @bae B x y -> forall n : nat, @bae B (bpow B x n) (bpow B y n).
Proof.
  intros B x y Hxy n. induction n as [| m IH].
  - apply (@bae_refl B).
  - change (bpow B x (Datatypes.S m)) with (@bmult B (bpow B x m) x).
    change (bpow B y (Datatypes.S m)) with (@bmult B (bpow B y m) y).
    apply (@bmult_wd B).
    + exact IH.
    + exact Hxy.
Qed.

(* exp 部分和对 bae 的传送（归纳 + bplus_wd/bmult_wd 逐级） *)
Lemma binv_esp_wd : forall (B : BanachAlg) (x y : (@BA B)),
  @bae B x y -> forall n : nat,
  @bae B (exp_series_partial B x n) (exp_series_partial B y n).
Proof.
  intros B x y Hxy n. induction n as [| m IH].
  - apply (@bae_refl B).
  - change (exp_series_partial B x (Datatypes.S m))
      with (@bplus B (exp_series_partial B x m)
              (@bmult B (bpow B x (Datatypes.S m))
                        (@bcoef B (/ q_fact (Datatypes.S m))))).
    change (exp_series_partial B y (Datatypes.S m))
      with (@bplus B (exp_series_partial B y m)
              (@bmult B (bpow B y (Datatypes.S m))
                        (@bcoef B (/ q_fact (Datatypes.S m))))).
    apply (@bplus_wd B).
    + exact IH.
    + apply (@bmult_wd B).
      * exact (binv_bpow_wd B x y Hxy (Datatypes.S m)).
      * apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* §1 S1 保底：(a+(−a))^n ≡ bzero（n≥1）                        *)
(* ============================================================ *)

(* n 归纳，bae 面逐级（bxb_bpow_zero 同款骨架，零在左经 §0）：  *)
(*   n=1：bone·(a+(−a)) ≡ a+(−a) ≡ bzero（plus_opp 消项）；     *)
(*   n=S(S j)：(a+(−a))^{S j} 已 ≡ bzero（IH），乘 (a+(−a))      *)
(*   后经左零消去收口——每级恰好消一个 plus_opp 因子。           *)
Lemma binv_bpow_opp_add : forall (B : BanachAlg) (a : (@BA B)) (n : nat),
  (1 <= n)%nat -> @bae B (bpow B (@bplus B a (@bopp B a)) n) (@bzero B).
Proof.
  intros B a n Hn. destruct n as [| m].
  - exfalso. lia.
  - induction m as [| j IH].
    + (* n = 1：bone·(a+(−a)) → a+(−a) → bzero *)
      change (bpow B (@bplus B a (@bopp B a)) (Datatypes.S 0%nat))
        with (@bmult B (@bone B) (@bplus B a (@bopp B a))).
      apply (@bae_trans B _ (@bplus B a (@bopp B a)) _).
      * exact (@bmult_one_l B (@bplus B a (@bopp B a))).
      * exact (@bplus_opp B a).
    + (* n = S (S j)：IH 消去首因子，左零收口 *)
      assert (Hj : (1 <= Datatypes.S j)%nat) by lia.
      change (bpow B (@bplus B a (@bopp B a)) (Datatypes.S (Datatypes.S j)))
        with (@bmult B (bpow B (@bplus B a (@bopp B a)) (Datatypes.S j))
                       (@bplus B a (@bopp B a))).
      apply (@bae_trans B _ (@bmult B (@bzero B) (@bplus B a (@bopp B a))) _).
      * apply (@bmult_wd B (bpow B (@bplus B a (@bopp B a)) (Datatypes.S j))
                           (@bplus B a (@bopp B a))
                           (@bzero B) (@bplus B a (@bopp B a))).
        -- exact (IH Hj).
        -- apply (@bae_refl B).
      * exact (binv_bmult_zero_l B (@bplus B a (@bopp B a))).
Qed.

(* 咬合证书：本席 S1 与 BXB 席零元幂终点经 bpow_wd 传送对位—— *)
(*   两席在 bzero 处终点一致，总装席可任取其一为 e^0 幂腿。      *)
Lemma binv_bpow_opp_add_mesh : forall (B : BanachAlg) (a : (@BA B)) (n : nat),
  (1 <= n)%nat ->
  @bae B (bpow B (@bplus B a (@bopp B a)) n) (bpow B (@bzero B) n).
Proof.
  intros B a n Hn.
  exact (binv_bpow_wd B (@bplus B a (@bopp B a)) (@bzero B)
           (@bplus_opp B a) n).
Qed.

(* S1 主锚（S4 终结腿部分和精确形态）：(a+(−a)) 级数每一部分和  *)
(* 恒等于 bone——e^0=1 在 Banach 层的全量部分和等式面（极限免费， *)
(* 与 BXB bxb_series_zero 咬合）。                              *)
Lemma binv_esp_opp_add : forall (B : BanachAlg) (a : (@BA B)) (n : nat),
  @bae B (exp_series_partial B (@bplus B a (@bopp B a)) n) (@bone B).
Proof.
  intros B a n.
  apply (@bae_trans B _ (exp_series_partial B (@bzero B) n) _).
  - exact (binv_esp_wd B (@bplus B a (@bopp B a)) (@bzero B)
             (@bplus_opp B a) n).
  - exact (bxb_series_zero B n).
Qed.

(* ============================================================ *)
(* §2 S2 保底（主件）：部分和乘积配对恒等                        *)
(* ============================================================ *)

(* 行折叠：柯西方块第 j 行 = c_j · esp m b（bsum_mult_l 左乘拉出 *)
(*   + esp_as_bsum 逆传送；c_j := a^j·coef(1/j!)）。             *)
Lemma binv_row_fold : forall (B : BanachAlg) (a b : (@BA B)) (m j : nat),
  @bae B (bsum B (Datatypes.S m)
             (fun i : nat =>
                @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                         (@bmult B (bpow B b i) (@bcoef B (/ q_fact i)))))
         (@bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                  (exp_series_partial B b m)).
Proof.
  intros B a b m j.
  apply (@bae_trans B _
    (@bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
             (bsum B (Datatypes.S m)
                (fun i : nat =>
                   @bmult B (bpow B b i) (@bcoef B (/ q_fact i))))) _).
  - exact (bsum_mult_l B (Datatypes.S m)
             (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
             (fun i : nat => @bmult B (bpow B b i) (@bcoef B (/ q_fact i)))).
  - apply (@bmult_wd B).
    + apply (@bae_refl B).
    + apply (@bae_sym B). exact (esp_as_bsum B b m).
Qed.

(* 首行（j=0）塌缩为 esp m b：c_0 = bone·coef(1/0!) ≡ bone。     *)
Lemma binv_row_zero : forall (B : BanachAlg) (b : (@BA B)) (m : nat),
  @bae B (@bmult B (@bmult B (@bone B) (@bcoef B (/ q_fact 0%nat)))
                   (exp_series_partial B b m))
         (exp_series_partial B b m).
Proof.
  intros B b m.
  assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
  apply (@bae_trans B _ (@bmult B (@bone B) (exp_series_partial B b m)) _).
  - apply (@bmult_wd B (@bmult B (@bone B) (@bcoef B (/ q_fact 0%nat)))
                       (exp_series_partial B b m)
                       (@bone B) (exp_series_partial B b m)).
    + rewrite Hq0.
      apply (@bae_trans B _ (@bcoef B 1%Q) _).
      * exact (@bmult_one_l B (@bcoef B 1%Q)).
      * exact (@bcoef_one B).
    + apply (@bae_refl B).
  - exact (@bmult_one_l B (exp_series_partial B b m)).
Qed.

(* S2 主件：esp m a · esp m (−a) ≡ esp m (−a) + Σ_{k<m} c_{S k}·esp m (−a)
   （配对余项恒等：柯西方块按行拉出后首行=第二因子整块，余行=    *)
(*   配对余项和；精确形式以 esp_prod_square + bsum_rot 实测定形。 *)
(*   与 S1 主锚扣合：右腿 a+(−a) 级数恒一，左侧余项经三角转置     *)
(*   （B3Sv2 批三）与 bpow_add 特例链在总装席合流）。             *)
Lemma binv_pair : forall (B : BanachAlg) (a : (@BA B)) (m : nat),
  @bae B (@bmult B (exp_series_partial B a m)
                   (exp_series_partial B (@bopp B a) m))
         (@bplus B (exp_series_partial B (@bopp B a) m)
                   (bsum B m
                      (fun k : nat =>
                         @bmult B (@bmult B (bpow B a (Datatypes.S k))
                                          (@bcoef B (/ q_fact (Datatypes.S k))))
                                  (exp_series_partial B (@bopp B a) m)))).
Proof.
  intros B a m.
  apply (@bae_trans B _
    (bsum B (Datatypes.S m)
       (fun j : nat =>
          bsum B (Datatypes.S m)
            (fun i : nat =>
               @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                        (@bmult B (bpow B (@bopp B a) i)
                                  (@bcoef B (/ q_fact i)))))) _).
  - (* 柯西方块（esp_prod_square 正向直连） *)
    exact (esp_prod_square B a (@bopp B a) m).
  - (* 行折叠 → 首行提出（rot）→ 首行塌缩 *)
    apply (@bae_trans B _
      (bsum B (Datatypes.S m)
         (fun j : nat =>
            @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                     (exp_series_partial B (@bopp B a) m))) _).
    + eapply bsum_ext.
      intros k Hk. exact (binv_row_fold B a (@bopp B a) m k).
    + apply (@bae_trans B _
        (@bplus B (@bmult B (@bmult B (@bone B) (@bcoef B (/ q_fact 0%nat)))
                            (exp_series_partial B (@bopp B a) m))
                  (bsum B m
                     (fun k : nat =>
                        @bmult B (@bmult B (bpow B a (Datatypes.S k))
                                         (@bcoef B (/ q_fact (Datatypes.S k))))
                                 (exp_series_partial B (@bopp B a) m)))) _).
      * exact (bsum_rot B m
            (fun j : nat =>
               @bmult B (@bmult B (bpow B a j) (@bcoef B (/ q_fact j)))
                        (exp_series_partial B (@bopp B a) m))).
      * apply (@bplus_wd_l B _ _ _).
        exact (binv_row_zero B (@bopp B a) m).
Qed.

(* ============================================================ *)
(* §3 S3 加分：对角线交错结构起步                                *)
(* ============================================================ *)

(* 加法逆的左乘换符号：(−x)·z ≡ −(x·z)（bdistrib_r + 左零 +      *)
(*   bopp_unique）。                                            *)
Lemma binv_bmult_opp_l : forall (B : BanachAlg) (x z : (@BA B)),
  @bae B (@bmult B (@bopp B x) z) (@bopp B (@bmult B x z)).
Proof.
  intros B x z.
  apply (@bopp_unique B (@bmult B (@bopp B x) z) (@bmult B x z)).
  apply (@bae_trans B _ (@bmult B (@bplus B (@bopp B x) x) z) _).
  - apply (@bae_sym B). exact (@bdistrib_r B (@bopp B x) x z).
  - apply (@bae_trans B _ (@bmult B (@bzero B) z) _).
    + apply (@bmult_wd B (@bplus B (@bopp B x) x) z (@bzero B) z).
      * apply (@bae_trans B _ (@bplus B x (@bopp B x)) _).
        -- exact (@bplus_comm B (@bopp B x) x).
        -- exact (@bplus_opp B x).
      * apply (@bae_refl B).
    + exact (binv_bmult_zero_l B z).
Qed.

(* 加法逆的右乘换符号：x·(−x) ≡ −(x·x)（bdistrib_l 镜像） *)
Lemma binv_mult_opp_r : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B x (@bopp B x)) (@bopp B (@bmult B x x)).
Proof.
  intros B x.
  apply (@bopp_unique B (@bmult B x (@bopp B x)) (@bmult B x x)).
  apply (@bae_trans B _ (@bmult B x (@bplus B (@bopp B x) x)) _).
  - apply (@bae_sym B). exact (@bdistrib_l B x (@bopp B x) x).
  - apply (@bae_trans B _ (@bmult B x (@bzero B)) _).
    + apply (@bmult_wd B x (@bplus B (@bopp B x) x) x (@bzero B)).
      * apply (@bae_refl B).
      * apply (@bae_trans B _ (@bplus B x (@bopp B x)) _).
        -- exact (@bplus_comm B (@bopp B x) x).
        -- exact (@bplus_opp B x).
    + exact (@bmult_zero B x).
Qed.

(* 左乘版（(−x)·x ≡ −(x·x)，与 binv_mult_opp_r 对偶） *)
Lemma binv_mult_opp_l : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B (@bopp B x) x) (@bopp B (@bmult B x x)).
Proof.
  intros B x.
  apply (@bopp_unique B (@bmult B (@bopp B x) x) (@bmult B x x)).
  apply (@bae_trans B _ (@bmult B (@bplus B (@bopp B x) x) x) _).
  - apply (@bae_sym B). exact (@bdistrib_r B (@bopp B x) x x).
  - apply (@bae_trans B _ (@bmult B (@bzero B) x) _).
    + apply (@bmult_wd B (@bplus B (@bopp B x) x) x (@bzero B) x).
      * apply (@bae_trans B _ (@bplus B x (@bopp B x)) _).
        -- exact (@bplus_comm B (@bopp B x) x).
        -- exact (@bplus_opp B x).
      * apply (@bae_refl B).
    + exact (binv_bmult_zero_l B x).
Qed.

(* a 与 −a 可换：a·(−a) ≡ (−a)·a（双臂各 ≡ −(a·a)）——          *)
(*   bpow_comm_r 的交换证书，幂次清项引擎接线位。                *)
Lemma binv_mult_opp_swap : forall (B : BanachAlg) (a : (@BA B)),
  @bae B (@bmult B a (@bopp B a)) (@bmult B (@bopp B a) a).
Proof.
  intros B a.
  apply (@bae_trans B _ (@bopp B (@bmult B a a)) _).
  - exact (binv_mult_opp_r B a).
  - apply (@bae_sym B). exact (binv_mult_opp_l B a).
Qed.

(* 双逆乘积：(−x)·(−x) ≡ x·x *)
Lemma binv_bmult_opp_opp : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B (@bopp B x) (@bopp B x)) (@bmult B x x).
Proof.
  intros B x.
  apply (@bae_trans B _ (@bopp B (@bmult B x (@bopp B x))) _).
  - exact (binv_bmult_opp_l B x (@bopp B x)).
  - apply (@bae_trans B _ (@bopp B (@bopp B (@bmult B x x))) _).
    + apply (@bopp_wd B). exact (binv_mult_opp_r B x).
    + apply (@bae_sym B).
      exact (@bopp_unique B (@bmult B x x) (@bopp B (@bmult B x x))
               (@bplus_opp B (@bmult B x x))).
Qed.

(* 偶次塌缩种子：bpow (−u) 2 ≡ bpow u 2（交错结构偶次项全正位） *)
Lemma binv_bpow_opp2 : forall (B : BanachAlg) (u : (@BA B)),
  @bae B (bpow B (@bopp B u) (Datatypes.S (Datatypes.S 0%nat)))
         (bpow B u (Datatypes.S (Datatypes.S 0%nat))).
Proof.
  intros B u.
  change (bpow B (@bopp B u) (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult B (@bmult B (@bone B) (@bopp B u)) (@bopp B u)).
  change (bpow B u (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult B (@bmult B (@bone B) u) u).
  apply (@bae_trans B _ (@bmult B (@bopp B u) (@bopp B u)) _).
  - apply (@bmult_wd B (@bmult B (@bone B) (@bopp B u)) (@bopp B u)
                       (@bopp B u) (@bopp B u)).
    + exact (@bmult_one_l B (@bopp B u)).
    + apply (@bae_refl B).
  - apply (@bae_trans B _ (@bmult B u u) _).
    + exact (binv_bmult_opp_opp B u).
    + apply (@bae_sym B).
      apply (@bmult_wd B (@bmult B (@bone B) u) u u u).
      * exact (@bmult_one_l B u).
      * apply (@bae_refl B).
Qed.

(* 乘法四元换位：(w·y)·(x·z) ≡ (w·x)·(y·z)（给定 y·x ≡ x·y；    *)
(*   bpow 拆分的六步清项链，bplus_swap4 的乘法镜像）。           *)
Lemma binv_bmult_swap4 : forall (B : BanachAlg) (w x y z : (@BA B)),
  @bae B (@bmult B y x) (@bmult B x y) ->
  @bae B (@bmult B (@bmult B w y) (@bmult B x z))
         (@bmult B (@bmult B w x) (@bmult B y z)).
Proof.
  intros B w x y z Hcomm.
  apply (@bae_trans B _ (@bmult B w (@bmult B y (@bmult B x z))) _).
  - apply (@bae_sym B). exact (@bmult_assoc B w y (@bmult B x z)).
  - apply (@bae_trans B _ (@bmult B w (@bmult B (@bmult B y x) z)) _).
    + apply (@bmult_wd B w (@bmult B y (@bmult B x z))
                       w (@bmult B (@bmult B y x) z)).
      * apply (@bae_refl B).
      * exact (@bmult_assoc B y x z).
    + apply (@bae_trans B _ (@bmult B w (@bmult B x (@bmult B y z))) _).
      * apply (@bmult_wd B w (@bmult B (@bmult B y x) z)
                         w (@bmult B x (@bmult B y z))).
        -- apply (@bae_refl B).
        -- apply (@bae_trans B _ (@bmult B (@bmult B x y) z) _).
           ++ apply (@bmult_wd B (@bmult B y x) z (@bmult B x y) z).
              ** exact Hcomm.
              ** apply (@bae_refl B).
           ++ apply (@bae_sym B). exact (@bmult_assoc B x y z).
      * exact (@bmult_assoc B w x (@bmult B y z)).
Qed.

(* 幂乘积分拆：(a·(−a))^k ≡ a^k·(−a)^k（归纳 + swap4 清项；      *)
(*   交换证书 = binv_mult_opp_swap 接 bpow_comm_r）。            *)
Lemma binv_bpow_split : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  @bae B (bpow B (@bmult B a (@bopp B a)) k)
         (@bmult B (bpow B a k) (bpow B (@bopp B a) k)).
Proof.
  intros B a k. induction k as [| j IH].
  - change (bpow B (@bmult B a (@bopp B a)) 0%nat) with (@bone B).
    change (@bmult B (bpow B a 0%nat) (bpow B (@bopp B a) 0%nat))
      with (@bmult B (@bone B) (@bone B)).
    apply (@bae_sym B). exact (@bmult_one_l B (@bone B)).
  - change (bpow B (@bmult B a (@bopp B a)) (Datatypes.S j))
      with (@bmult B (bpow B (@bmult B a (@bopp B a)) j)
                     (@bmult B a (@bopp B a))).
    change (bpow B a (Datatypes.S j)) with (@bmult B (bpow B a j) a).
    change (bpow B (@bopp B a) (Datatypes.S j))
      with (@bmult B (bpow B (@bopp B a) j) (@bopp B a)).
    apply (@bae_trans B _
      (@bmult B (@bmult B (bpow B a j) (bpow B (@bopp B a) j))
                (@bmult B a (@bopp B a))) _).
    + apply (@bmult_wd B (bpow B (@bmult B a (@bopp B a)) j)
                         (@bmult B a (@bopp B a))
                         (@bmult B (bpow B a j) (bpow B (@bopp B a) j))
                         (@bmult B a (@bopp B a))).
      * exact IH.
      * apply (@bae_refl B).
    + exact (binv_bmult_swap4 B (bpow B a j) a
                (bpow B (@bopp B a) j) (@bopp B a)
                (bpow_comm_r B (@bopp B a) a
                   (@bae_sym B _ _ (binv_mult_opp_swap B a)) j)).
Qed.

(* 标量折并：(x·cq)·(y·cr) ≡ (x·y)·coef(q·r)（bcoef_comm 换位 +  *)
(*   bcoef_mult 折并；对角线项双 1/k! 系数的归并引擎）。          *)
Lemma binv_bmult_coef_fold : forall (B : BanachAlg) (x y : (@BA B)) (q r : Q),
  @bae B (@bmult B (@bmult B x (@bcoef B q)) (@bmult B y (@bcoef B r)))
         (@bmult B (@bmult B x y) (@bcoef B (q * r)%Q)).
Proof.
  intros B x y q r.
  apply (@bae_trans B _
    (@bmult B x (@bmult B (@bcoef B q) (@bmult B y (@bcoef B r)))) _).
  - apply (@bae_sym B).
    exact (@bmult_assoc B x (@bcoef B q) (@bmult B y (@bcoef B r))).
  - apply (@bae_trans B _
      (@bmult B x (@bmult B (@bmult B y (@bcoef B q)) (@bcoef B r))) _).
    + (* cq·(y·cr) ≡ (cq·y)·cr ≡ (y·cq)·cr *)
      apply (@bmult_wd B x (@bmult B (@bcoef B q) (@bmult B y (@bcoef B r)))
                       x (@bmult B (@bmult B y (@bcoef B q)) (@bcoef B r))).
      * apply (@bae_refl B).
      * apply (@bae_trans B _
          (@bmult B (@bmult B (@bcoef B q) y) (@bcoef B r)) _).
        -- exact (@bmult_assoc B (@bcoef B q) y (@bcoef B r)).
        -- apply (@bmult_wd B (@bmult B (@bcoef B q) y) (@bcoef B r)
                             (@bmult B y (@bcoef B q)) (@bcoef B r)).
           ++ apply (@bae_sym B). exact (@bcoef_comm B q y).
           ++ apply (@bae_refl B).
    + (* x·(y·(cq·cr)) ≡ x·(y·coef(q r)) ≡ (x·y)·coef(q r) *)
      apply (@bae_trans B _
        (@bmult B x (@bmult B y (@bcoef B (q * r)%Q))) _).
      * apply (@bae_trans B _
          (@bmult B x (@bmult B y (@bmult B (@bcoef B q) (@bcoef B r)))) _).
        -- apply (@bmult_wd B x (@bmult B (@bmult B y (@bcoef B q)) (@bcoef B r))
                             x (@bmult B y (@bmult B (@bcoef B q) (@bcoef B r)))).
           ++ apply (@bae_refl B).
           ++ apply (@bae_sym B).
              exact (@bmult_assoc B y (@bcoef B q) (@bcoef B r)).
        -- apply (@bmult_wd B x (@bmult B y (@bmult B (@bcoef B q) (@bcoef B r)))
                             x (@bmult B y (@bcoef B (q * r)%Q))).
           ++ apply (@bae_refl B).
           ++ apply (@bmult_wd B y (@bmult B (@bcoef B q) (@bcoef B r))
                                y (@bcoef B (q * r)%Q)).
              ** apply (@bae_refl B).
              ** apply (@bae_sym B). exact (@bcoef_mult B q r).
      * exact (@bmult_assoc B x y (@bcoef B (q * r)%Q)).
Qed.

(* 对角线主项定义：D_k := (a^k/k!)·((−a)^k/k!) *)
Definition binv_diag_term (B : BanachAlg) (a : (@BA B)) (k : nat) : (@BA B) :=
  @bmult B (@bmult B (bpow B a k) (@bcoef B (/ q_fact k)))
           (@bmult B (bpow B (@bopp B a) k) (@bcoef B (/ q_fact k))).

(* 对角线项的幂次交错折叠：D_k ≡ (a·(−a))^k · coef((1/k!)·(1/k!))
   —— 交错符号载体全部收入幂底 a·(−a)（≡ −(a·a)），其偶次 ≡ a^{2k}
   （binv_bpow_opp2 种子），奇次 ≡ −(a^{2k})；Q 侧系数恒正          *)
(*   (1/k!)²，为后续 Σ_{k≤m} (−1)^k a^{2k}/(k!)² 交错和的起步位。  *)
Lemma binv_diag_term_pair : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  @bae B (binv_diag_term B a k)
         (@bmult B (bpow B (@bmult B a (@bopp B a)) k)
                   (@bcoef B ((/ q_fact k) * (/ q_fact k))%Q)).
Proof.
  intros B a k.
  apply (@bae_trans B _
    (@bmult B (@bmult B (bpow B a k) (bpow B (@bopp B a) k))
             (@bcoef B ((/ q_fact k) * (/ q_fact k))%Q)) _).
  - exact (binv_bmult_coef_fold B (bpow B a k) (bpow B (@bopp B a) k)
                                (/ q_fact k) (/ q_fact k)).
  - apply (@bmult_wd B).
    + exact (@bae_sym B _ _ (binv_bpow_split B a k)).
    + apply (@bae_refl B).
Qed.

(* 偶次主项种子连接：(a·(−a))² ≡ (a·a)·(a·a)——偶次交错项的全正   *)
(*   坍缩起步（配合 binv_bpow_opp2 给出 D_{2j} 的 a^{4j} 朝向）。 *)
Lemma binv_bpow_oppmult2 : forall (B : BanachAlg) (a : (@BA B)),
  @bae B (bpow B (@bmult B a (@bopp B a)) (Datatypes.S (Datatypes.S 0%nat)))
         (@bmult B (@bmult B a a) (@bmult B a a)).
Proof.
  intros B a.
  change (bpow B (@bmult B a (@bopp B a)) (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult B (@bmult B (@bone B) (@bmult B a (@bopp B a)))
                   (@bmult B a (@bopp B a))).
  apply (@bae_trans B _
    (@bmult B (@bmult B a (@bopp B a)) (@bmult B a (@bopp B a))) _).
  - apply (@bmult_wd B (@bmult B (@bone B) (@bmult B a (@bopp B a)))
                       (@bmult B a (@bopp B a))
                       (@bmult B a (@bopp B a)) (@bmult B a (@bopp B a))).
    + exact (@bmult_one_l B (@bmult B a (@bopp B a))).
    + apply (@bae_refl B).
  - apply (@bae_trans B _
      (@bmult B (@bmult B a a) (@bmult B (@bopp B a) (@bopp B a))) _).
    + (* (a·(−a))·(a·(−a)) ≡ (a·a)·((−a)·(−a))：swap4 对称向 *)
      apply (@bae_sym B).
      exact (binv_bmult_swap4 B a (@bopp B a) a (@bopp B a)
                (binv_mult_opp_swap B a)).
    + apply (@bmult_wd B (@bmult B a a) (@bmult B (@bopp B a) (@bopp B a))
                         (@bmult B a a) (@bmult B a a)).
      * apply (@bae_refl B).
      * exact (binv_bmult_opp_opp B a).
Qed.

(* ============================================================ *)
(* 对接注记（S4 可逆性特例主链位置，不落承认件）：               *)
(*   ① S1 幂腿：binv_bpow_opp_add（n≥1 全量零，plus_opp 逐级消  *)
(*     项，零二项式系数）+ binv_bpow_opp_add_mesh（与 BXB 终点   *)
(*     对位）+ binv_esp_opp_add（e^0=1 部分和恒一主锚）。        *)
(*   ② S2 乘积腿：binv_pair（配对余项恒等）——右侧第二因子整块   *)
(*     提出，余行=配对余项和；总装席经三角转置（B3Sv2 批三）     *)
(*     将余项归零后与 binv_esp_opp_add 合流即 S4。               *)
(*   ③ S3 对角线：binv_diag_term_pair（幂底收于 a·(−a) ≡ −(a·a)）*)
(*     + 偶次种子 binv_bpow_opp2/binv_bpow_oppmult2——交错结构    *)
(*     的符号载体已全部入幂底，Q 侧系数面 (1/k!)² 恒正。         *)
(*   分工边界：一般 bpow_add = 席 BA 领地（本席零触碰）；        *)
(*   汇合点 = exp_add 总装席（下一批）。                          *)
(* ============================================================ *)
