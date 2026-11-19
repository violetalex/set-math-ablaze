# 常见故障

先跑 `mathlean doctor`，它会把下面大部分情况直接指出来。

## 环境

**`PATH 里没有 lake`**
装 elan：`curl https://elan.lean-lang.org | sh`，然后重开终端。`mathlean` 会自动把
`~/.elan/bin` 加到子进程的 PATH，但 `lake build` 里的 `lake` 仍然需要 elan 装好。

**`找不到 Mathlib`**
`mathlean.ini` 的 `[lean] mathlib` 要指向 Mathlib 的**源码目录**（含 `Mathlib/` 子目录），
不是 `.olean` 目录。默认值是工程内的 `.lake/packages/mathlib`（相对工程根解析）。
也可以设环境变量 `MATHLEAN_MATHLIB`。

**第一次 `lake build` 很慢**
正常。`new` 会把 `.lake/packages` 链接到共用目录，但本工程自己的构建产物仍然要生成一次
（约 45 秒）。之后增量。

**`Error in the HTTP2 framing layer`**
lake 在尝试下载依赖。说明 `.lake/packages` 没链接成功，见上。

## 门禁

**`sorry` 门报了注释里的 sorry**
不该发生——扫描器会剥离注释和字符串。如果你看到这种情况，多半是嵌套块注释写法超出了
扫描器的支持（它支持任意嵌套）。用 `mathlean check --json` 拿到确切行号核对。

**`sorryAx` 出现在公理列表里**
说明某个 `theorem` 里有没补完的证明，或者你 `#print axioms` 的是个用 `sorry` 定义的声明。
`lake build` 只给警告，所以必须靠这道门。

**`依赖未登记公理 X`**
源码里有 `axiom X : ...`。两件事选一件：
在 `mathlean.ini` 的 `[axioms]` 里登记并写明论文中对应物，或者把证明改成不用它的。

**`Audit.lean 里没有 #print axioms Foo.bar`**
台账里写了 `PROVED`，但 `Audit.lean` 没审它。加一行：

```lean
#print axioms Foo.bar
```

**`源码里找不到声明 Foo.bar`**
三种可能：拼错了；声明在 `namespace Foo` 里而台账只写了 `bar`（这个其实能匹配上）；
或者文件根本没进 `import` 链（`Foo.lean` 只 import 了部分子模块）。

**`依赖图存在环：C1 → C2 → C1`**
这是最值钱的一条报错。数学上等价的两个命题互相依赖，通常意味着你在用结论证结论。
处理办法：把其中一条降级为 `CONDITIONAL` 并写出它真正依赖的假设。

**台账行没被解析到**
必须是**六列**，第一列是 `C1` 这种 ID，且不在代码块里：

```
| ID | 状态 | 命题 | Lean 声明 | 依赖 | 备注 |
|---|---|---|---|---|---|
| C1 | PROVED | 偶数加偶数 | IsEven.add | — | 样例 |
```

模板里的 `| _ | OPEN | ... |` 是占位行，会被跳过。

## 工具本身

**`ImportError: No module named mathlean`**
工程里的 `tools/` 丢了。跑 `mathlean upgrade --root <工程>`（需要有 `lakefile.toml`）。

**工程里的门禁行为和仓库里的不一致**
工程用的是创建时的版本。`cat tools/VERSION` 看版本，`mathlean upgrade` 更新。

**改了检查器，测试挂了**
先跑 `python3 -I run_tests.py -v`，再跑 `mathlean selfcheck`。两者都过才算没改坏。
