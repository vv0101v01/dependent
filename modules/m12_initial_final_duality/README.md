# Module M12：`m12_initial_final_duality`（始代數—終共同代數 Chu 對偶、去森林化雙變形融合、雙模擬局部化與內在語法反射）

本模組為第二階段範疇對偶與跨層融合模組，聯合 **M8（嚴格正歸納／IR／II／容器 $W$-樹）**、**M9（共同代數與無窮流）**、**M6（64-bit Chu 空間與伽羅瓦對應）**、**M1（DAG 雜湊駐留 Arena）** 與 **M3（雙向 NbE 核心）**，將有限歸納結構與無限共同代數觀測放入同一自對偶 Chu 矩陣中，實作去森林化雙變形（Hylomorphism Deforestation）、雙模擬局部化範疇 $\mathsf{Coalg}[\mathsf{Bisim}^{-1}]$ 之 $O(1)$ 整數 ID 駐留，以及歸納-歸納內在伸縮語法至依賴類型核心之函子反射。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定理 M12.T1（始代數有限觀測模式與終共同代數無窮流之 Chu-Galois 自對偶定理）**：`build_algebra_coalgebra_chu` 將有限容器觀測樹 `WTree` 與無窮流 `InfStream` 配對為 64-bit `ChuTypingSpace`，嚴格滿足鏡像對偶 $(C^\perp)^\perp = C$ 與位元級伽羅瓦伴隨律 $T \subseteq s(S) \iff S \subseteq t(T)$。
2. **定理 M12.T2（Meijer-Fokkinga-Paterson 去森林化雙變形融合定理）**：對任意有界展開共同代數 `coalg` 與摺疊代數 `alg`，去森林化管線 `hylo_deforest` 在完全不配置中間 `WTree` 堆積節點之前提下，計算結果與先展開再摺疊嚴格相等：
   $$\mathsf{hylo\_deforest}(\gamma, \alpha, s) \;=\; \mathsf{cata\_w}(\alpha,\ \mathsf{ana\_w}(\gamma, s))$$
3. **定理 M12.T3（雙模擬局部化 $\mathsf{Coalg}[\mathsf{Bisim}^{-1}]$ 與 $O(1)$ Arena 駐留完備定理）**：`minimize_stream_coalgebra` 將任意含不可達死狀態或冗餘迴圈之有限狀態流自動機約化為唯一典範最小套索商自動機，再經 `localize_coalgebra_to_arena_id` 駐留於 M1 `SyntaxArena` 後，將無限視界雙模擬弱等價強行升格為 $O(1)$ 整數相等：
   $$M_1 \sim_{\mathrm{bisim}} M_2 \iff \mathsf{localize\_coalgebra\_to\_arena\_id}(M_1) = \mathsf{localize\_coalgebra\_to\_arena\_id}(M_2)$$
4. **定理 M12.T4（歸納-歸納內在語法至雙向 NbE 核心反射健全性定理）**：任意通過 M8 互鎖良構檢驗之 `(IICtx, IITy)` 經 `reflect_ii_ctx_and_certify_ty` 反射後，必構成 M3 `JudgmentCtx` 下良類型之語義核心類型；基底類按**精確有限基數**反射：$|El| = 0 \mapsto \mathsf{Empty}$、$|El| = 1 \mapsto \mathbf{1}$、$|El| \ge 2 \mapsto \mathbb{N}$。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 代數—共同代數 64-bit Chu 空間建構器 (`eval_w_pattern_on_stream`, `build_algebra_coalgebra_chu`) | `initial_final_duality.mbt` | $O(\|W\| \cdot \|S\|)$ 建表；伽羅瓦查詢 $O(1)$ 位元運算 | 跨有限樹與無窮流建立 `UInt64` 對偶伴隨矩陣 |
| 去森林化雙變形管線 (`ana_w`, `hylo_deforest`) | `initial_final_duality.mbt` | $O(\text{展開節點數})$ 零中間樹記憶體配置 | 消除中間代數資料結構配置開銷 |
| 雙模擬商最小化與 M1 Arena 局部化器 (`minimize_stream_coalgebra`, `localize_coalgebra_to_arena_id`) | `initial_final_duality.mbt` | 最小化後駐留比對嚴格 $O(1)$ | 結合並查集雙模擬、BFS 典範重編號與 64-bit FNV-1a 雜湊駐留 |
| 歸納-歸納至 NbE 核心反射編譯器 (`compile_ii_ty_to_core`, `reflect_ii_ctx_and_certify_ty`) | `initial_final_duality.mbt` | $O(\|\Gamma\| + \|T\|)$ | 打通 M8 互鎖語法與 M3 Kripke NbE 核心 |

---

## 三、資料夾視角的依賴關係圖

```text
  [m1_syntax_context]  [m3_pi_sigma_types]  [m6_chu_galois_bridge]  [m8_inductive_family]  [m9_coalgebra_stream]
           │                    │                     │                       │                      │
           └────────────────────┴─────────────────────┼───────────────────────┴──────────────────────┘
                                                      ▼
                                   ┌─────────────────────────────────────┐
                                   │     dtt/m12_initial_final_duality   │
                                   │      initial_final_duality.mbt      │
                                   └──────────────────┬──────────────────┘
                                                      │
                                                      ▼
                                     [ dtt/m14_phase2_unified_system ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `eval_w_pattern_on_stream` 執行有限觀測樹對無窮流之配對評估，交由 `build_algebra_coalgebra_chu` 封裝為 M6 `ChuTypingSpace`。
2. `hylo_deforest` 直接串接展開與摺疊算子。
3. `minimize_stream_coalgebra` 調用 M9 並查集雙模擬對狀態空間取商並規範化編號，再由 `localize_coalgebra_to_arena_id` 寫入 M1 `SyntaxArena`。
4. `reflect_ii_ctx_and_certify_ty` 將 M8 `(IICtx, IITy)` 映射至 M3 `JudgmentCtx` 並執行語義良類型驗證。

### 輸出公共接口（Public API）
- **錯誤類型**：`DualityError`。
- **核心函式**：`eval_w_pattern_on_stream`, `build_algebra_coalgebra_chu`, `ana_w`, `hylo_deforest`, `minimize_stream_coalgebra`, `localize_coalgebra_to_arena_id`, `compile_ii_ty_to_core`, `reflect_ii_ctx_and_certify_ty`。
