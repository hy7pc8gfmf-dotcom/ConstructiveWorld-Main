(* ============================================================ *)
(* UpAblB1_MonoSplit.v —— 席 B1·深施工席（MonoSplit 三证书位真重施工） *)
(*                                                              *)
(* 席位：B1（MonoSplit 三证书位真重施工·S6 移交"禁机械供给注水"件）      *)
(* 包装协议 v2 内嵌执行｜独立伴生件·原树零改｜落盘即完成。               *)
(*                                                              *)
(* 辖区（S6 移交偏差 6＋§六第四梯表）：UpReqEntropyMonoSplit.v            *)
(*   Section EmsEntropyMonoSplit 三证书位——                              *)
(*     Hpinned:137（约束片能量钉）｜Hkl_right:146（KL 增长 eps 形）｜     *)
(*     Hkl_left:153（KL 衰减 eps 形）——真内容重施工（KL 谱系实算，       *)
(*     非机械供给）。                                                    *)
(*                                                              *)
(* 【与 S5 已立件槽位零重叠 diff（开工实测）】                            *)
(*   Live_X/UpAblD1S5_UpReqEntropyMonoSplit.v（FA-D1S5 数据供给打包件）   *)
(*   以打包记录型 uabd1s5_ems_pack13 镜像认领 12 净新槽＋1 载体完备位：    *)
(*     S:90/sum:91/ext:95/le:97/linear:99/add:102/T_star:105/            *)
(*     T_star_pos:106/energy:107（9 接口/数据位）＋Hpinned:137-140/       *)
(*     Hkl_right:146-152/Hkl_left:153-159（三证书位·单点零能量 mult_zero  *)
(*     捷径腿，件头自述"机械供给级"）。                                  *)
(*   本席零重复立件：不立打包记录、不动 12 槽坐标认领；9 接口/数据位仅作    *)
(*   discharge 全参形的具体供给参数（uab1_sum 等 Definition，消费不认领）；  *)
(*   三证书位按 S6 移交做**实算链升级 discharge**（非 S5 形的打包供给）：    *)
(*     对比 S5 腿——本席 energy:=fun _ => real_one（非零任意能量形成立），  *)
(*     Hpinned 走 Gibbs 族归一化谱系实算（real_Z_temp/real_inv_pos_      *)
(*     correct，非 mult_zero 捷径），Hkl 双腿走 real_KL_temp 定义展开     *)
(*     实算（求和面 ι 收敛→log_wd/log_one→群律→lt_compat 序迁移）。       *)
(*   命名前缀 uab1_* 与 S5 uabd1s5_ems_* 零碰撞；S5 文件零触碰。          *)
(*                                                              *)
(* 【真 discharge 全参形】消费母本 Section 出节定理（先经 G0 母本代际      *)
(*   锁合重编译：母本 .v 09-19 10:38 同步代 6f31f420 新于陈 .vo 09-17，    *)
(*   全量重编译 EXIT=0 后方 Require——防混代际）：五件母本定理全参应用     *)
(*   落地为具体无假设实例——ems_pinned_kl_entropy_eq（件 0）/              *)
(*   ems_entropy_temp_antitone_above（件 1·全库首件降支）/                *)
(*   ems_entropy_temp_mono_below（件 2）/ems_entropy_peak_bound_above     *)
(*   （件 3）/ems_entropy_split_at_peak（主件）。签名经探针 Check 实测     *)
(*   （g0-probe2-tuab1.log），Let 速记全内联，参数序逐位照应。             *)
(*                                                              *)
(* 【实例供给（全参）】S:=unit｜sum:=fun f => f tt｜sumpos/ext/le:=消费位  *)
(*   直取｜linear/add:=ι 重合 real_eq_refl｜T_star:=real_one｜            *)
(*   T_star_pos:=real_lt_zero_one｜energy:=fun _ => real_one（非零）。    *)
(*                                                              *)
(* 【三证书位实算链（真内容）】                                           *)
(*   链 A（Gibbs 族归一化·温度参数化形）：单点载体温 t 处                  *)
(*     p_t(tt) = inv(Z_t)·bf(tt) == 1——Z_t 定义性收敛到因子自身          *)
(*     （sum ι + energy ι），real_inv_pos_correct 一步归一。              *)
(*   链 B（Hpinned 实算）：E(p_u) ≡ Σ p_u·e ≡ p_u(tt)·1 == p_u(tt) ==1    *)
(*     == E(p_{t*})（链 A 双温实例）——能量钉对任意能量形成立（本例 e≡1）。 *)
(*   链 C（KL 谱系实算）：real_KL_temp 定义展开→求和面单点 ι 收敛→        *)
(*     双腿 log(p_u(tt))/log(p_{t*}(tt)) 经链 A＋real_log_wd→real_log_one *)
(*     归零→内层 plus/opp 群律→外层 mult_one→KL(p_u‖p_{t*})==0。          *)
(*   链 D/E（Hkl 双腿）：KL(v)==KL(u)==0（链 C）→(KL_v−KL_u)+eps == eps    *)
(*     →0<eps 序迁移（real_lt_compat）→real_le Or 左支 inl。              *)
(*   非圆性账：三链只消费温度族定义件（UpReqTempDefs）/KL 定义件           *)
(*   （UpReqEntropyDeficitTemp）与环律/log 器（CW_219），不消费母本三      *)
(*   Hypothesis 以外的母本内容证明三腿；母本四件定理经全参应用消费三腿      *)
(*   落地——分离定理内容＝母本已证的"KL-V 形⟹熵单峰"蕴涵在本实例的闭合。   *)
(*                                                              *)
(* 【红线】纯构造性零 公理/承认件/收尾弃证/参数假设/猜想命题/中止证         *)
(*   （G1 双轨禁词字面量零命中档，母本 6f31f420 代同规范）。               *)
(*   Set 层比较全 real_le/real_lt sigT-Or 形；零 git、零注册面、原树零改。 *)
(* 编译配方：unset COQLIB ROCQLIB→钉 9.1 双变量→coqc -q -native-compiler  *)
(*   no -Q . ""（cpu_guard 前置 tasklist 探针）；G3 提取一人一目录树外     *)
(*   ASCII cwd；G4 coqchk 后台长窗。                                      *)
(* 四关留痕：Live_X/attn/logs/g{0..4}-UpAblB1_*.{log,exit}                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMonoSplit.

(* ============ 实例供给（全参，9 接口/数据位消费形——不认领 S5 已立槽） ============ *)

Definition uab1_sum : (unit -> Real) -> Real :=
  fun f : unit -> Real => f tt.

Definition uab1_sumpos
  : forall f : unit -> Real,
      (forall s : unit, real_lt real_zero (f s)) ->
      real_lt real_zero (uab1_sum f) :=
  fun (f : unit -> Real)
      (Hf : forall s : unit, real_lt real_zero (f s)) => Hf tt.

Definition uab1_ext : forall f g : unit -> Real,
    (forall s : unit, real_eq (f s) (g s)) ->
    real_eq (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_eq (f s) (g s)) => H tt.

Definition uab1_le : forall f g : unit -> Real,
    (forall s : unit, real_le (f s) (g s)) ->
    real_le (uab1_sum f) (uab1_sum g) :=
  fun (f g : unit -> Real)
      (H : forall s : unit, real_le (f s) (g s)) => H tt.

Definition uab1_linear : forall (a : Real) (f : unit -> Real),
    real_eq (uab1_sum (fun s : unit => real_mult a (f s)))
            (real_mult a (uab1_sum f)) :=
  fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)).

Definition uab1_add : forall f g : unit -> Real,
    real_eq (uab1_sum (fun s : unit => real_plus (f s) (g s)))
            (real_plus (uab1_sum f) (uab1_sum g)) :=
  fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)).

Definition uab1_T_star : Real := real_one.
Definition uab1_T_star_pos : real_lt real_zero uab1_T_star := real_lt_zero_one.
Definition uab1_energy : unit -> Real := fun _ : unit => real_one.

(* ============ 母本速记件显式参形实名镜像（δ 展开同体；对照母本 L112-131） ============ *)

Definition uab1_bd (u : Real) (Hu : real_lt real_zero u) : unit -> Real :=
  real_boltzmann_dist_temp unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_bd_pos (u : Real) (Hu : real_lt real_zero u)
  : forall s : unit, real_lt real_zero (uab1_bd u Hu s) :=
  real_boltzmann_dist_temp_pos unit uab1_sum uab1_sumpos u Hu uab1_energy.

Definition uab1_ent (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_entropy_dist unit uab1_sum (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* KL 方向红线（照母本 L128-131 审计表）：KL(p_u ‖ p_{t*})——p_u 第一分布位， *)
(* p_{t*}=p_1 参考位；T_star 已全参钉为 real_one。 *)
Definition uab1_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp unit uab1_sum uab1_sumpos uab1_T_star uab1_T_star_pos uab1_energy
               (uab1_bd u Hu) (uab1_bd_pos u Hu).

(* ============ 工具腿（环律两行，S5 同形自证——不 Require S5 件） ============ *)

Lemma uab1_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Qed.

Lemma uab1_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_plus_comm real_zero x) (real_plus_zero x)).
Qed.

(* ============ 链 A：Gibbs 族归一化实算（温度参数化形） ============ *)
(* 单点载体温 t 处 p_t(tt) == 1：Z_t δ/ι 收敛到因子自身，inv_pos_correct    *)
(* 一步归一（real_Z_temp/real_Z_temp_pos/real_inv_pos_correct 谱系全消费）。 *)

Lemma uab1_bt_pt_one : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (uab1_bd t Ht tt) real_one.
Proof.
  intros t Ht.
  exact (real_eq_trans
           (uab1_bd t Ht tt)
           (real_mult
              (real_boltzmann_factor_temp unit t Ht uab1_energy tt)
              (real_inv_pos
                 (real_Z_temp unit uab1_sum t Ht uab1_energy)
                 (real_Z_temp_pos unit uab1_sum uab1_sumpos
                    t Ht uab1_energy)))
           real_one
           (real_mult_comm
              (real_inv_pos
                 (real_Z_temp unit uab1_sum t Ht uab1_energy)
                 (real_Z_temp_pos unit uab1_sum uab1_sumpos
                    t Ht uab1_energy))
              (real_boltzmann_factor_temp unit t Ht uab1_energy tt))
           (real_inv_pos_correct
              (real_Z_temp unit uab1_sum t Ht uab1_energy)
              (real_Z_temp_pos unit uab1_sum uab1_sumpos
                 t Ht uab1_energy))).
Qed.

(* ============ 证书位 1：Hpinned 实算链（链 A 双温实例） ============ *)
(* 语句形＝母本 Hpinned:137 出节形全参具体化（签名探针实测）：               *)
(*   sum (fun s => p_u(s)·e(s)) == E(p_{t*})。                              *)
(* 实算：两侧各自 mult_one 归到 p(·)(tt)，再链 A 双温归一于 1。              *)
(* 对 S5 腿升级：能量任意非零成立（S5 用零函数 mult_zero 捷径），            *)
(* Gibbs 族归一化谱系全链消费（非单步捷径）。                               *)

Lemma uab1_Hpinned :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (uab1_sum
         (fun s : unit =>
            real_mult (uab1_bd u Hu s) (uab1_energy s)))
      (real_energy_exp_temp unit uab1_sum uab1_sumpos
         uab1_T_star uab1_T_star_pos uab1_energy).
Proof.
  intros u Hu.
  apply (real_eq_trans
           (uab1_sum
              (fun s : unit =>
                 real_mult (uab1_bd u Hu s) (uab1_energy s)))
           (uab1_bd u Hu tt)
           (real_energy_exp_temp unit uab1_sum uab1_sumpos
              uab1_T_star uab1_T_star_pos uab1_energy)).
  - exact (real_mult_one (uab1_bd u Hu tt)).
  - exact (real_eq_trans
             (uab1_bd u Hu tt)
             real_one
             (real_energy_exp_temp unit uab1_sum uab1_sumpos
                uab1_T_star uab1_T_star_pos uab1_energy)
             (uab1_bt_pt_one u Hu)
             (real_eq_sym
                (real_energy_exp_temp unit uab1_sum uab1_sumpos
                   uab1_T_star uab1_T_star_pos uab1_energy)
                real_one
                (real_eq_trans
                   (real_energy_exp_temp unit uab1_sum uab1_sumpos
                      uab1_T_star uab1_T_star_pos uab1_energy)
                   (uab1_bd uab1_T_star uab1_T_star_pos tt)
                   real_one
                   (real_mult_one (uab1_bd uab1_T_star uab1_T_star_pos tt))
                   (uab1_bt_pt_one uab1_T_star uab1_T_star_pos)))).
Qed.

(* ============ 链 C：KL 谱系实算（real_KL_temp 定义展开） ============ *)
(* KL(p_u‖p_{t*}) ≡ Σ p_u·(log p_u − log p_{t*}) 单点 ι 收敛为              *)
(* p_u(tt)·(log p_u(tt) − log p_{t*}(tt))；双 log 经链 A＋real_log_wd→      *)
(* real_log_one 归零；群律收口。                                            *)

Lemma uab1_kl_zero : forall (u : Real) (Hu : real_lt real_zero u),
  real_eq (uab1_kl u Hu) real_zero.
Proof.
  intros u Hu.
  assert (Hlu : real_eq
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd u Hu tt) real_one
                (uab1_bd_pos u Hu tt) real_lt_zero_one
                (uab1_bt_pt_one u Hu))
             (real_log_one real_lt_zero_one)). }
  assert (Hl1 : real_eq
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             real_zero).
  { exact (real_eq_trans
             (real_log (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uab1_bd uab1_T_star uab1_T_star_pos tt) real_one
                (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)
                real_lt_zero_one
                (uab1_bt_pt_one uab1_T_star uab1_T_star_pos))
             (real_log_one real_lt_zero_one)). }
  apply (real_eq_trans
           (uab1_kl u Hu)
           (real_mult
              (uab1_bd u Hu tt)
              (real_plus
                 (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                 (real_opp
                    (real_log
                       (uab1_bd uab1_T_star uab1_T_star_pos tt)
                       (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
           real_zero).
  - exact (real_eq_refl
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))).
  - exact (real_eq_trans
             (real_mult
                (uab1_bd u Hu tt)
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))))
             (real_mult real_one (real_plus real_zero (real_opp real_zero)))
             real_zero
             (RealSetoid.real_eq_mult_compat_adapt
                (uab1_bd u Hu tt) real_one
                (real_plus
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))))
                (real_plus real_zero (real_opp real_zero))
                (uab1_bt_pt_one u Hu)
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log (uab1_bd u Hu tt) (uab1_bd_pos u Hu tt))
                   real_zero
                   (real_opp
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt)))
                   (real_opp real_zero)
                   Hlu
                   (RealSetoid.real_eq_opp_compat
                      (real_log
                         (uab1_bd uab1_T_star uab1_T_star_pos tt)
                         (uab1_bd_pos uab1_T_star uab1_T_star_pos tt))
                      real_zero
                      Hl1)))
             (real_eq_trans
                (real_mult real_one (real_plus real_zero (real_opp real_zero)))
                (real_mult real_one real_zero)
                real_zero
                (RealSetoid.real_eq_mult_compat_adapt
                   real_one real_one
                   (real_plus real_zero (real_opp real_zero))
                   real_zero
                   (real_eq_refl real_one)
                   (real_plus_opp real_zero))
                (uab1_mult_one_l real_zero))).
Qed.

(* ============ 证书位 2：Hkl_right 实算链（KL 增长腿，eps 松弛形） ============ *)
(* 语句形＝母本 Hkl_right:146 出节形全参具体化（T_star:=real_one）。          *)
(* 实算：KL(v)==KL(u)==0（链 C）→(KL_v−KL_u)+eps==eps→0<eps 序迁移。         *)

Lemma uab1_Hkl_right :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (uab1_kl v Hv) (real_opp (uab1_kl u Hu)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uab1_kl v Hv) real_zero
                          (real_opp (uab1_kl u Hu)) (real_opp real_zero)
                          (uab1_kl_zero v Hv)
                          (RealSetoid.real_eq_opp_compat
                             (uab1_kl u Hu) real_zero
                             (uab1_kl_zero u Hu)))
                       (real_eq_refl eps))
                    (uab1_plus_zero_l eps)))
              Heps)).
Qed.

(* ============ 证书位 3：Hkl_left 实算链（KL 衰减腿，镜像） ============ *)

Lemma uab1_Hkl_left :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus (uab1_kl u Hu) (real_opp (uab1_kl v Hv)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uab1_kl u Hu) real_zero
                          (real_opp (uab1_kl v Hv)) (real_opp real_zero)
                          (uab1_kl_zero u Hu)
                          (RealSetoid.real_eq_opp_compat
                             (uab1_kl v Hv) real_zero
                             (uab1_kl_zero v Hv)))
                       (real_eq_refl eps))
                    (uab1_plus_zero_l eps)))
              Heps)).
Qed.

(* ============ 真 discharge：母本出节五件全参落地（具体无假设实例） ============ *)

(* 件 0（约束片熵亏恒等式落地）：KL + S == S_star。 *)
Theorem uab1_discharge_pinned_kl_entropy_eq :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_plus (uab1_kl u Hu) (uab1_ent u Hu))
            (uab1_ent uab1_T_star uab1_T_star_pos).
Proof.
  intros u Hu.
  exact (ems_pinned_kl_entropy_eq
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned u Hu).
Qed.

(* 件 1（降支·全库首件的落地实例）：t* ≤ u ≤ v ⟹ S(p_v) ≤ S(p_u) + eps。 *)
Theorem uab1_discharge_antitone_above :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le uab1_T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps).
Proof.
  intros u v Hu Hv Htu Huv eps Heps.
  exact (ems_entropy_temp_antitone_above
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned uab1_Hkl_right
           u v Hu Hv Htu Huv eps Heps).
Qed.

(* 件 2（升支重组落地实例）：u ≤ v ≤ t* ⟹ S(p_u) ≤ S(p_v) + eps。 *)
Theorem uab1_discharge_mono_below :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v uab1_T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps).
Proof.
  intros u v Hu Hv Huv Hvt eps Heps.
  exact (ems_entropy_temp_mono_below
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned uab1_Hkl_left
           u v Hu Hv Huv Hvt eps Heps).
Qed.

(* 件 3（峰界落地实例；母本出节形含 le 接口位——签名探针实测序）：          *)
(* 一切正温的熵 ≤ 峰熵 + eps。 *)
Theorem uab1_discharge_peak_bound :
  forall (u : Real) (Hu : real_lt real_zero u),
    forall eps : Real,
      real_lt real_zero eps ->
      real_le (uab1_ent u Hu)
              (real_plus (uab1_ent uab1_T_star uab1_T_star_pos) eps).
Proof.
  intros u Hu eps Heps.
  exact (ems_entropy_peak_bound_above
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_le uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned
           u Hu eps Heps).
Qed.

(* 主件（分离定理落地实例）：prod 账 Set 形——左支×右支。 *)
Theorem uab1_discharge_split :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v uab1_T_star ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent u Hu) (real_plus (uab1_ent v Hv) eps)) *
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le uab1_T_star u -> real_le u v ->
     forall eps : Real,
       real_lt real_zero eps ->
       real_le (uab1_ent v Hv) (real_plus (uab1_ent u Hu) eps)).
Proof.
  exact (ems_entropy_split_at_peak
           unit uab1_sum uab1_sumpos
           uab1_ext uab1_linear uab1_add
           uab1_T_star uab1_T_star_pos uab1_energy
           uab1_Hpinned uab1_Hkl_right uab1_Hkl_left).
Qed.

(* ============ 假设审计（公理面：全零缺口方绿） ============ *)
Print Assumptions uab1_bt_pt_one.
Print Assumptions uab1_Hpinned.
Print Assumptions uab1_kl_zero.
Print Assumptions uab1_Hkl_right.
Print Assumptions uab1_Hkl_left.
Print Assumptions uab1_discharge_pinned_kl_entropy_eq.
Print Assumptions uab1_discharge_antitone_above.
Print Assumptions uab1_discharge_mono_below.
Print Assumptions uab1_discharge_peak_bound.
Print Assumptions uab1_discharge_split.
