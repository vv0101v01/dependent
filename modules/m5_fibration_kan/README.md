# Module M5：`m5_fibration_kan`（Grothendieck 理解纖維化、左右 Kan 擴張、語境纖維積／理論推出與層黏合）

本模組為第一層範疇融合模組，聯合 **M1（語法與顯式代換語境）**、**M2（代數累積宇宙）** 與 **M3（$\Pi/\Sigma$ 雙向檢驗與 NbE）**，建立 Grothendieck 理解纖維化（Comprehension Fibration）$\int_{\mathcal{C}\text{tx}} \mathsf{Ty} \to \mathcal{C}\text{tx}$、顯示投影之左右 Kan 擴張三元伴隨 $\Sigma_\pi \dashv \pi^* \dashv \Pi_\pi$、語境纖維積（對偶於語法理論融合推出）、Beck-Chevalley 自然同構驗證、Grothendieck 覆蓋截面層黏合（Sheaf Gluing）及 Operad 纖維推導樹嫁接。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定義 M5.D1（雙向函子橋接 $\mathsf{SynExpr} \leftrightarrows \mathsf{CoreTm}$）**：將 M1 具備 $O(1)$ 位元摘要之語法樹與 M3 語義 NbE 核心項互譯，並將結構化伸縮語境 `Context` 反射為語義 `JudgmentCtx`。
2. **定理 M5.T1（Grothendieck 劈裂笛卡兒提升函子性定理）**：語境態射複合 `compose_ctx_morphisms(f, g)` 與劈裂重索引 `cartesian_reindex` 嚴格滿足 $(g \circ f)^*(A) = f^*(g^*(A))$ 及 $\mathsf{id}_\Gamma^*(A) = A$，且保持 M2 代數宇宙小性階。
3. **定理 M5.T2（左右 Kan 擴張伴隨實現定理）**：沿 $r$ 步顯示投影態射 $\pi_r : (\Gamma, \Delta_r) \to \Gamma$，左 Kan 擴張 $\mathsf{Lan}_{\pi_r}$ 由迭代 $\Sigma$-類型精確實現，右 Kan 擴張 $\mathsf{Ran}_{\pi_r}$ 由迭代 $\Pi$-類型精確實現，小性階滿足最小上界封閉 $\bigsqcup_{k=1}^r \ell(D_k) \sqcup \ell(A)$。
4. **定理 M5.T3（語境拉回／理論融合推出對偶與 Beck-Chevalley 自然同構定理）**：對共享基底 $\Gamma_0$ 之語境擴張 $\Gamma_1 = (\Gamma_0, \Delta_1)$ 與 $\Gamma_2 = (\Gamma_0, \Delta_2)$，`build_context_pullback` 構造 $\mathcal{C}\text{tx}$ 中之纖維積 $\Gamma_1 \times_{\Gamma_0} \Gamma_2$（即對偶範疇 $\mathcal{C}\text{tx}^{\mathrm{op}}$ 中語法理論之融合推出 $\Gamma_1 \sqcup_{\Gamma_0} \Gamma_2$），且左右 Kan 擴張皆滿足嚴格 NbE $\beta\eta$-定義同構：
   $$\pi_1^*(\mathsf{Lan}_{\pi_2}(A)) \;\equiv_{\beta\eta}\; \mathsf{Lan}_{p_1}(p_2^*(A)), \qquad \pi_1^*(\mathsf{Ran}_{\pi_2}(A)) \;\equiv_{\beta\eta}\; \mathsf{Ran}_{p_1}(p_2^*(A))$$
5. **定理 M5.T4（Grothendieck 覆蓋截面層黏合定理）**：局部截面 $s_1 \in \mathsf{Tm}(\Gamma_1), s_2 \in \mathsf{Tm}(\Gamma_2)$ 若在錨定限制態射下經 M3 NbE 驗證滿足 $a_1^*(s_1) \equiv_{\beta\eta} a_2^*(s_2)$，則可唯一提升並黏合為拉回頂點 $\Gamma_1 \times_{\Gamma_0} \Gamma_2$ 上之全局認證截面配對。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 語法與核心項雙向函子橋 (`syn_to_core`, `core_to_syn`, `reflect_ctx_to_m3`) | `fibration_kan_pushout.mbt` | $O(\|e\|)$ | 自動重建 M1 64-bit 位元摘要與 FNV-1a 雜湊，並對接 M3 雙向 NbE |
| 語境態射代數與劈裂笛卡兒重索引 (`id_ctx_morphism`, `display_projection_morphism`, `compose_ctx_morphisms`, `cartesian_reindex`) | `fibration_kan_pushout.mbt` | $O(\|\text{cod}\| + \|A\|)$ | 轉譯語境態射為 M1 嚴格化 $\sigma$-代換並保持宇宙小性 |
| 左右 Kan 擴張合成器 (`left_kan_sigma`, `right_kan_pi`, `estimate_syn_smallness`) | `fibration_kan_pushout.mbt` | $O(r + \|A\|)$ | 沿任意 $r$ 步顯示投影自動合成 $\Sigma/\Pi$ 伸縮類型與小性上界 |
| 語境纖維積／理論推出構造器 (`build_context_pullback`) | `fibration_kan_pushout.mbt` | $O(\|\Gamma_1\| + \|\Gamma_2\|)$ | 精確偏移跨語境依賴索引並產生典範投影態射 $(p_1, p_2)$ |
| Beck-Chevalley 同構檢驗器 (`verify_beck_chevalley`) | `fibration_kan_pushout.mbt` | 多項式於正規化規模 | 同時檢驗 $\Sigma$ 左伴隨與 $\Pi$ 右伴隨在拉回方塊上之語義交換性 |
| 局部截面層黏合與 Operad 纖維嫁接器 (`glue_compatible_local_terms`, `graft_and_verify_fibered_operad`) | `fibration_kan_pushout.mbt` | $O(\|s_1\| + \|s_2\|)$ | 以 NbE 驗證重疊截面相容性，並對多插槽開放項執行帶類型嫁接 |

---

## 三、資料夾視角的依賴關係圖

```text
    [ dtt/m1_syntax_context ]   [ dtt/m2_universe_cumul ]   [ dtt/m3_pi_sigma_types ]
                │                           │                           │
                └───────────────────────────┼───────────────────────────┘
                                            ▼
                         ┌─────────────────────────────────────┐
                         │        dtt/m5_fibration_kan         │
                         │      fibration_kan_pushout.mbt      │
                         └──────────────────┬──────────────────┘
                                            │
                                            ▼
                                [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. 由 `syn_to_core` / `core_to_syn` / `reflect_ctx_to_m3` 連接 M1 語法語境與 M3 語義域。
2. `CtxMorphism` 與 `FibredType` 組織基範疇與全範疇物件，透過 `morphism_to_subst` 驅動 `cartesian_reindex`、`left_kan_sigma` 與 `right_kan_pi`。
3. `build_context_pullback` 建立拉回頂點與投影對，交由 `verify_beck_chevalley` 與 `glue_compatible_local_terms` 進行範疇同構與層黏合檢驗。

### 輸出公共接口（Public API）
- **類型與錯誤**：`FibredType`, `CtxMorphism`, `ContextPullbackSquare`, `FibrationError`。
- **橋接與纖維化函子**：`syn_to_core`, `core_to_syn`, `reflect_ctx_to_m3`, `id_ctx_morphism`, `display_projection_morphism`, `morphism_to_subst`, `compose_ctx_morphisms`, `cartesian_reindex`, `estimate_syn_smallness`。
- **Kan 擴張、拉回、Beck-Chevalley、層黏合與 Operad**：`left_kan_sigma`, `right_kan_pi`, `build_context_pullback`, `verify_beck_chevalley`, `glue_compatible_local_terms`, `graft_and_verify_fibered_operad`。
