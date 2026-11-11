# Module M7：`m7_unified_kernel`（大一統依賴類型論認證核心、半直積語境作用與伸縮短正合序列）

本模組為最高層大一統核心模組，匯流並融合 **M1..M6 全部六個下層模組**，完整打通「位元摘要顯式代換語法 $\to$ 代數與無煩擾累積宇宙求解 $\to$ $\Pi/\Sigma$ 雙向 Kripke NbE 核心 $\to$ 柯里-霍華德證明消除與見證提取 $\to$ Grothendieck 纖維化與 Kan 擴張 $\to$ 64 位元 Chu 空間與全域伽羅瓦對應」之端到端機械認證管線，並新增 **反擬陣相容語境自同構與代換半直積（Semidirect Product）** 及 **依賴伸縮短正合序列分裂障礙類（Short Exact Sequence Splitting Obstruction）**。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定理 M7.T1（累積與非累積雙模態大一統認證健全性定理）**：`UnifiedKernel::certify_dtt_theorem` 聯合 M1 DAG 雜湊駐留、M2 伽羅瓦宇宙差分圖可滿足性與 M3 雙向 NbE 檢驗，在 `Cumulative` 模態下精確允許協變宇宙提升 $\mathcal{U}_{\min} \preceq \mathcal{U}_{\text{decl}}$，在 `NonCumulative` 模態下嚴格強制唯一性 $\mathcal{U}_{\min} = \mathcal{U}_{\text{decl}}$，並完成無煩擾小性編解碼 $\Uparrow_i(\Downarrow_i A) \equiv_{\beta} A$ 之語義正規化。
2. **定理 M7.T2（端到端柯里-霍華德證明消除、純程式提取與核心重認證定理）**：`UnifiedKernel::certify_curry_howard_proof` 對任一 M4 構造性證明執行迂迴消元與證明抹除提取純計算見證（`ExtractedProg`），再經 M6 雙命名空間編譯器與 M5 語法反射嵌入統一伸縮語境，由 M3 NbE 核心從零獨立重驗通過。
3. **定理 M7.T3（反擬陣相容語境自同構與纖維代換半直積同態定理）**：語境置換 $\pi \in \mathfrak{S}_n$ 合法當且僅當對所有依賴關係 $d \prec_{\mathrm{dep}} l$ 保持 $\pi(d) < \pi(l)$；半直積複合 `compose_semidirect(g2, g1)` 嚴格滿足作用同態律：
   $$\mathsf{apply\_subst}(\mathsf{apply\_subst}(e, \llbracket g_1 \rrbracket),\ \llbracket g_2 \rrbracket) \;=\; \mathsf{apply\_subst}(e, \llbracket g_2 \rtimes g_1 \rrbracket)$$
4. **定理 M7.T4（依賴伸縮短正合序列分裂判準與截面合成定理）**：對短正合序列 $0 \to \Delta_{\mathrm{fib}} \xrightarrow{\iota} (\Gamma_{\mathrm{base}}.\Delta_{\mathrm{fib}}) \xrightarrow{\pi} \Gamma_{\mathrm{base}} \to 0$（輸入強制 $0 \le \mathrm{base\_len} \le |\Gamma_{\mathrm{total}}|$，違者 `InvalidBaseLength`），一階導出分裂障礙秩 `obstruction_rank == 0` 當且僅當 $\Delta_{\mathrm{fib}}$ 中所有纖維假設皆可沿 $O(1)$ 位元遮罩強化跨越 $\Gamma_{\mathrm{base}}$；此時 `synthesize_splitting_section` 要求**每條纖維假設恰有一個閉**預設見證（`FiberDefaultCountMismatch` / `NonClosedFiberDefault`），並構造分裂截面 $s : \Gamma_{\mathrm{base}} \to (\Gamma_{\mathrm{base}}.\Delta_{\mathrm{fib}})$ 嚴格滿足 $\pi \circ s = \mathsf{id}_{\Gamma_{\mathrm{base}}}$。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 大一統核心狀態與變數假設器 (`UnifiedKernel::new`, `assume_variable`) | `unified_kernel.mbt` | 均攤 $O(\|\Gamma\| + \|T\|)$ | 同步維護 DAG Arena、伸縮語境與伽羅瓦宇宙差分圖 |
| 依賴類型論雙模態定理認證器 (`UnifiedKernel::certify_dtt_theorem`) | `unified_kernel.mbt` | 多項式於正規化規模 | 整合 M1 雜湊駐留、M2 模態宇宙檢查與 M3 $\beta\eta$ 正規形式提取 |
| 端到端柯里-霍華德跨體系認證管線 (`UnifiedKernel::certify_curry_howard_proof`) | `unified_kernel.mbt` | $O(\|p\|)$ 編譯 + NbE 重驗 | 自動消除證明迂迴、提取計算見證並在統一 DTT 核心完成二次獨立檢驗 |
| 反擬陣自同構檢驗與半直積複合器 (`verify_admissible_context_automorphism`, `semidirect_to_subst`, `compose_semidirect`) | `unified_kernel.mbt` | $O(n^2)$ 位元檢查 / $O(n \cdot \|t\|)$ 複合 | 利用 `occ_mask` $O(1)$ 測試變數依賴並計算交叉代換乘積 |
| 伸縮短正合序列障礙分析與分裂截面合成器 (`analyze_telescope_exact_sequence`, `synthesize_splitting_section`) | `unified_kernel.mbt` | $O(\|\Delta_{\mathrm{fib}}\| \cdot \|\Gamma_{\mathrm{base}}\|)$ 位元測試 | 強制驗證 `base_len` 界與每纖維一閉預設見證；計算纖維對基底耦合秩，零障礙時自動強化纖維並合成右逆截面 $s$ |
| 全域核心遙測與不變量巡檢器 (`UnifiedKernel::collect_telemetry`) | `unified_kernel.mbt` | 多項式於核心規模 | 匯總 Arena 節點數、Ramsey-Dilworth 宇宙鏈高／反鏈寬、Chu-Galois 與 Beck-Chevalley 狀態 |

---

## 三、資料夾視角的依賴關係圖

```text
  [m1_syntax_context] [m2_universe_cumul] [m3_pi_sigma_types] [m4_curry_howard_prop]
           │                   │                   │                    │
           ├───────────────────┼───────────────────┤                    │
           │                   │                   ▼                    │
           │                   │          [m5_fibration_kan]            │
           │                   │                   │                    │
           ├───────────────────┴─────────┬─────────┼────────────────────┘
           │                             ▼         │
           │                  [m6_chu_galois_bridge]
           │                             │         │
           └─────────────────────────────┼─────────┘
                                         ▼
                          ┌──────────────────────────────┐
                          │     dtt/m7_unified_kernel    │
                          │      unified_kernel.mbt      │
                          └──────────────────────────────┘
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. 使用者透過 `UnifiedKernel::new(mode)` 初始化核心，呼叫 `assume_variable` 建立全局語境。
2. 依賴類型宣告進入 `certify_dtt_theorem`；構造性邏輯證明進入 `certify_curry_howard_proof`（串聯 M4 $\to$ M6 $\to$ M5 $\to$ M1/M2/M3），產出 `CertifiedArtifact`。
3. 語境對稱性與正合分裂分析分別由 `compose_semidirect` 與 `analyze_telescope_exact_sequence` / `synthesize_splitting_section` 執行，最終由 `collect_telemetry` 輸出全局統計與範疇公理巡檢報告。

### 輸出公共接口（Public API）
- **類型與錯誤**：`UnifiedKernel`, `CertifiedArtifact`, `KernelTelemetry`, `SemidirectCtxElem`, `TelescopeExactAnalysis`, `KernelError`。
- **核心認證與遙測方法**：`UnifiedKernel::{new, assume_variable, certify_dtt_theorem, certify_curry_howard_proof, collect_telemetry}`。
- **代數與同調組合算子**：`verify_admissible_context_automorphism`, `semidirect_to_subst`, `compose_semidirect`, `analyze_telescope_exact_sequence`, `synthesize_splitting_section`。
