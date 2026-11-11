# Module M1：`m1_syntax_context`（類型、項、顯式代換與單純形擬陣上下文）

本模組為獨立基礎模組（零跨模組依賴），涵蓋依賴類型論之核心語法層：**類型（Type）**、**項（Term）**、**顯式代換演算（$\sigma$-Calculus）**、**上下文望遠鏡（Context Telescope）**、**單純形退化與面映射（Simplicial Complex Maps）**、**上下文依賴擬陣獨立系統（Dependency Matroid Independence）**、**有色操作子嫁接（Colored Operad Grafting）** 及 **雜湊駐留有向無環圖（Hash-Consed Syntax Arena）**。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **定義 M1.D1（內蘊位元摘要語法節點 `SynExpr`）**：每個廣義代數語法項 $e$ 攜帶 64 位元自由 De Bruijn 索引遮罩 $\mathsf{occ\_mask}(e) \in \mathbb{B}^{64}$、嚴格自由變數深度上界 $\mathsf{max\_free}(e) \in \mathbb{N}$、操作子插槽遮罩 $\mathsf{slot\_mask}(e) \in \mathbb{B}^{64}$ 與 SplitMix64 結構雜湊值 $\mathsf{hash64}(e)$。
2. **局部公理 M1.A1（顯式代換之局部邏輯消元律）**：在嚴格化 $\sigma$-演算（Kaposi & Pujet, ICFP 2025）下，變數查詢滿足局部消元：
   $$v_0[t \cdot \sigma] \mapsto t, \qquad v_{n+1}[t \cdot \sigma] \mapsto v_n[\sigma], \qquad v_i[\Uparrow^k \sigma] \mapsto \begin{cases} v_i & i < k \\ (v_{i-k}[\sigma])[\uparrow^k] & i \ge k \end{cases}$$
3. **命題 M1.P1（常數時間 $O(1)$ 閉項與依賴退化判準）**：
   - $e$ 為閉項（無任何自由變數）若且唯若 $\mathsf{max\_free}(e) = 0$。
   - 依賴函數類型 $\Pi(x:A).B$ 或依賴乘積類型 $\Sigma(x:A).B$ 退化為非依賴函數 $A \to B$ 或笛卡兒積 $A \times B$ 若且唯若 $(\mathsf{occ\_mask}(B) \mathbin{\&} 1) = 0$，判定時間複雜度為 $O(1)$。
   - 當 $\mathsf{max\_free}(e) \le k$ 時，$e[\Uparrow^k \sigma] = e$ 以 $O(1)$ 時間直接短路返回，無須遍歷語法樹。
4. **引理 M1.L1（De Bruijn 索引與層級之鏡像對稱對合律）**：於長度為 $d$ 之上下文 $\Gamma$ 中，$\mathsf{idx\_to\_lvl}(d, i) = d - 1 - i$ 與 $\mathsf{lvl\_to\_idx}(d, l) = d - 1 - l$ 互為 $O(1)$ 嚴格對合雙射：$\mathsf{lvl\_to\_idx}(d, \mathsf{idx\_to\_lvl}(d, i)) = i$。
5. **定理 M1.T1（上下文單純形恆等式與強化消元定理）**：設 $\sigma_k(\Gamma, W)$ 為於層級 $k$ 插入假設 $W$ 之單純形退化弱化映射，$\delta_k(\Gamma)$ 為當後續假設對層級 $k$ 無傳遞依賴時之單純形面強化映射，則恆成立單純形收縮恆等式 $\delta_k(\sigma_k(\Gamma, W)) = \Gamma$。
6. **定理 M1.T2（上下文依賴擬陣反鏈交換律）**：以傳遞依賴位元遮罩 $\mathsf{trans\_lvl\_mask}$ 定義上下文層級偏序，所有互不傳遞依賴之層級子集構成獨立系統（擬陣反鏈族）；相鄰獨立假設 $l, l+1$ 經對換代換 `swap_adjacent_independent` 重編碼後，嚴格保持後續所有依賴項之類型語意不變。
7. **定理 M1.T3（有色操作子插槽嫁接結合律與雜湊駐留唯一性）**：帶拘束深度自動平移之操作子嫁接運算 $\mathsf{operad\_graft}$ 滿足操作子結合律 $(H \circ_0 M) \circ_1 N = H \circ_0 (M \circ_1 N)$；且於 `SyntaxArena` 中結構全等之語法樹映射至唯一常數級句柄 ID。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 位元並行自由變數與依賴檢測引擎 (`is_closed`, `depends_on_var0`, `has_free_var`) | `syntax_bitmask.mbt` | $O(1)$（64 內層變數及任意閉項） | 單指令 64 位元遮罩位元與運算 + `max_free` 嚴格上界短路 |
| 精確傳遞依賴查詢 (`lvl_depends_on`) | `context_matroid_operad.mbt` | 64 級內 $O(1)$；越窗 $O(d^2)$ 精確工作表掃描（遇窗即 $O(1)$ 短路） | 64-bit `trans_lvl_mask` 精確位元測試；64 層以上以 `has_free_var` 精確直接依賴工作表掃描，完全消除深層傳遞依賴假陰性 |
| 嚴格化 $\sigma$-代換智慧複合與短路求值 (`subst_compose`, `apply_subst`) | `sigma_subst.mbt` | $O(1)$ 複合 / $O(1)$ 閉子樹跳過 | 消除 `Var(0)·Shift(1)=Id`、`Lift` 合併與 `is_identity_upto` 零拷貝短路 |
| De Bruijn 索引 $\leftrightarrow$ 層級鏡像轉換與平坦望遠鏡查找 (`lookup_type_by_idx`) | `context_matroid_operad.mbt` | $O(1)$ 陣列定位 | 連續陣列儲存望遠鏡 + 鏡像對稱座標轉換 |
| 單純形弱化與強化映射 (`simplicial_weaken_at`, `simplicial_strengthen_at`) | `context_matroid_operad.mbt` | $O(\|\Gamma\|)$ 遮罩檢測 | 利用每項預先計算之 `trans_lvl_mask` 於 $O(1)$ 判斷單步依賴阻斷 |
| 上下文依賴擬陣獨立集判定與相鄰獨立假設對換 (`is_matroid_independent_set`, `swap_adjacent_independent`) | `context_matroid_operad.mbt` | $O(\min(\|\Gamma\|, 64))$ 位元交集 | 位元遮罩交集判定獨立集，並自動構造局部對換代換 `Lift(k, #1·#0·↑2)` |
| 有色操作子多插槽同步嫁接 (`operad_graft`) | `context_matroid_operad.mbt` | 無插槽子樹 $O(1)$ 短路 | 透過 `slot_mask` 跳過無插槽子樹，自動按累積拘束深度平移插入項 |
| SplitMix64 雜湊駐留有向無環圖 (`SyntaxArena::intern`) | `context_matroid_operad.mbt` | 均攤 $O(1)$ 駐留與全等比較 | 64 位元雪崩雜湊桶索引，將深層語法樹全等轉化為 `Int32` 整數比較 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │         dtt/m1_syntax_context               │
             │  syntax_bitmask.mbt ──► sigma_subst.mbt     │
             │          └──────────┬──────────┘            │
             │                     ▼                       │
             │        context_matroid_operad.mbt           │
             └──────────────┬──────────────┬───────────────┘
                            │              │
          ┌─────────────────┘              └─────────────────┐
          ▼                                                  ▼
[ dtt/m5_fibration_kan ]                         [ dtt/m6_chu_galois_bridge ]
          │                                                  │
          └────────────────────────┬─────────────────────────┘
                                   ▼
                        [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `syntax_bitmask.mbt`：建構 `SynExpr` 時即時以 $O(1)$ 合成子節點之 `occ_mask`、`slot_mask`、`max_free` 與 `hash64`。
2. `sigma_subst.mbt`：接收 `SynExpr` 與 `Subst`，利用 `max_free` 執行 $O(1)$ 恆等代換短路，對開放子樹遞迴下推 `Lift` 並執行變數強化 `try_strengthen_expr`。
3. `context_matroid_operad.mbt`：在 `Context` 擴展時將索引遮罩鏡像映射為層級遮罩並累積傳遞閉包 `trans_lvl_mask`，供單純形面映射、擬陣獨立交換、最小支撐集切片、操作子插槽嫁接與 `SyntaxArena` 駐留使用。

### 輸出公共接口（Public API）
- **類型與錯誤**：`SynKind`, `SynExpr`, `Subst`, `CtxEntry`, `Context`, `SyntaxArena`, `SyntaxError`。
- **語法建構子**：`mk_var`, `mk_hole`, `mk_univ`, `mk_poly_univ`, `mk_prop_sort`, `mk_small_encode`, `mk_small_decode`, `mk_pi`, `mk_arrow`, `mk_lam`, `mk_app`, `mk_sigma`, `mk_pair`, `mk_fst`, `mk_snd`, `mk_unit_ty`, `mk_unit_val`, `mk_empty_ty`, `mk_absurd`, `mk_sum_ty`, `mk_inl`, `mk_inr`, `mk_case_sum`, `mk_nat_ty`, `mk_zero`, `mk_succ`, `mk_nat_rec`, `mk_id_ty`, `mk_refl`, `mk_j_elim`, `mk_squash_ty`, `mk_squash_intro`, `mk_const_ref`。
- **代換與位元查詢**：`SynExpr::is_closed`, `SynExpr::depends_on_var0`, `SynExpr::has_free_var`, `shift_expr_simple`, `subst_id`, `subst_shift`, `subst_cons`, `subst_single`, `subst_lift`, `subst_compose`, `lookup_subst`, `apply_subst`, `try_strengthen_expr`。
- **上下文、擬陣、操作子與駐留池**：`idx_to_lvl`, `lvl_to_idx`, `Context::empty`, `Context::extend_var`, `Context::extend_def`, `Context::lookup_type_by_idx`, `Context::lookup_entry_by_lvl`, `Context::lvl_depends_on`, `Context::simplicial_weaken_at`, `Context::simplicial_strengthen_at`, `Context::is_matroid_independent_set`, `Context::swap_adjacent_independent`, `Context::minimal_support_mask`, `operad_graft`, `mk_bool_ty`, `mk_bool_lit`, `SyntaxArena::new`, `SyntaxArena::intern`。
