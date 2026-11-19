// Claude Code workflow: 数学命题求解 + Lean 4/Mathlib 机器验证
//
//   Workflow({ scriptPath: "~/math-lean/workflow.js",
//              args: { root: "~/my-problem", problem: "要证什么", rounds: 2 } })
//
// 每个阶段对应 WORKFLOW.md 的 P0–P9。所有产物落到 <root>/docs 与 <root>/<Lib>。

export const meta = {
  name: 'math-lean',
  description: '数学命题求解 + Lean 4/Mathlib 验证：陈述锁定→文献→证明⇄反例⇄审计→形式化→保真→终检',
  phases: [
    { title: 'Spec', detail: 'P0 陈述锁定' },
    { title: 'Literature', detail: 'P1 引用核实' },
    { title: 'Proof', detail: 'P2 两条独立路线 + 引理 DAG' },
    { title: 'Attack', detail: 'P3/P4 四路反例 + 三 lens 审计' },
    { title: 'Formalize', detail: 'P5 形式化映射' },
    { title: 'Lean', detail: 'P6 逐引理实现并编译' },
    { title: 'Fidelity', detail: 'P7 陈述保真审计' },
    { title: 'Writeup', detail: 'P8/P9 台账、成文、终检' },
  ],
}

const SPEC_SCHEMA = {
  type: 'object',
  properties: {
    title: { type: 'string' },
    objects: { type: 'array', items: { type: 'string' } },
    hypotheses: { type: 'array', items: { type: 'string' } },
    conclusion: { type: 'string' },
    falsifiers: { type: 'array', items: { type: 'string' } },
    needs_literature: { type: 'boolean' },
    notes: { type: 'string' },
  },
  required: ['title', 'objects', 'hypotheses', 'conclusion', 'falsifiers', 'needs_literature'],
}

const LEMMAS_SCHEMA = {
  type: 'object',
  properties: {
    route: { type: 'string' },
    lemmas: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          statement: { type: 'string' },
          proof: { type: 'string' },
          deps: { type: 'array', items: { type: 'string' } },
          status: { enum: ['PROVED-INFORMAL', 'CONDITIONAL', 'OPEN'] },
        },
        required: ['id', 'statement', 'proof', 'deps', 'status'],
      },
    },
  },
  required: ['route', 'lemmas'],
}

const CITATIONS_SCHEMA = {
  type: 'object',
  properties: {
    entries: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          key: { type: 'string' },
          full: { type: 'string' },
          identifier: { type: 'string' },
          relevance: { type: 'string' },
        },
        required: ['key', 'full', 'identifier', 'relevance'],
      },
    },
  },
  required: ['entries'],
}

const VERIFY_SCHEMA = {
  type: 'object',
  properties: {
    verdict: { enum: ['VERIFIED', 'REJECTED'] },
    reason: { type: 'string' },
    correction: { type: 'string' },
  },
  required: ['verdict', 'reason'],
}

const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          target: { type: 'string' },
          lens: { type: 'string' },
          summary: { type: 'string' },
          detail: { type: 'string' },
          severity: { enum: ['fatal', 'major', 'minor'] },
        },
        required: ['target', 'lens', 'summary', 'detail', 'severity'],
      },
    },
  },
  required: ['findings'],
}

const JUDGE_SCHEMA = {
  type: 'object',
  properties: {
    verdict: { enum: ['CONFIRMED', 'PLAUSIBLE', 'REFUTED'] },
    reason: { type: 'string' },
  },
  required: ['verdict', 'reason'],
}

// Lean 实现 agent 的返回值：靠"文本是否以 OK 开头"判断成败太脆——agent 写了一段
// 正常的诊断说明（"已经存在，编译通过，验证如下……"）就会被当成 FAIL，
// 进而把整条依赖链卡死。改成结构化返回。
const LEAN_SCHEMA = {
  type: 'object',
  properties: {
    status: { enum: ['OK', 'FAIL'] },
    detail: { type: 'string' },
  },
  required: ['status', 'detail'],
}

const FORMAL_SCHEMA = {
  type: 'object',
  properties: {
    items: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          lean_name: { type: 'string' },
          mathlib_ready: { type: 'string' },
          effort: { enum: ['easy', 'medium', 'hard', 'not-feasible'] },
          notes: { type: 'string' },
        },
        required: ['id', 'lean_name', 'mathlib_ready', 'effort', 'notes'],
      },
    },
  },
  required: ['items'],
}

const FIDELITY_SCHEMA = {
  type: 'object',
  properties: {
    items: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          lean_name: { type: 'string' },
          verdict: { enum: ['MATCH', 'WEAKER', 'STRONGER', 'DIFFERENT'] },
          detail: { type: 'string' },
        },
        required: ['id', 'lean_name', 'verdict', 'detail'],
      },
    },
  },
  required: ['items'],
}

// P8 产物审计：写文件的 agent 说"我写了"不算数，另起一个 agent 去磁盘上看。
const ARTIFACT_SCHEMA = {
  type: 'object',
  properties: {
    files: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          path: { type: 'string' },
          bytes: { type: 'number' },
          empty: { type: 'boolean' },
        },
        required: ['path', 'bytes', 'empty'],
      },
    },
    missing: { type: 'array', items: { type: 'string' } },
    empty: { type: 'array', items: { type: 'string' } },
  },
  required: ['files', 'missing', 'empty'],
}

const root = (args && args.root) || '.'
const problem = typeof args === 'string' ? args : ((args && args.problem) || '')
const maxRounds = Math.max(1, Math.min(4, (args && args.rounds) || 2))
const lib = (args && args.lib) || ''

// 攻击阶段必须有预算上限：agent 挂掉时返回 null，不加限制会被"每条意见三个裁判"拖爆。
const attackBudget = Math.max(4, Math.min(120, (args && args.attack_budget) || 24))
const maxFindingsPerRound = Math.max(1, (args && args.max_findings) || 6)

const say = (m) => log(m)

// 关键阶段的 agent 返回 null（被跳过、报错、余额不足……）不能当成"没有结果"继续跑。
// 这一步不自带重试：一个阶段的核心 agent 都没返回，后面的阶段全是空转。
const failures = []
const must = (stage, what, value) => {
  if (value === null || value === undefined) {
    failures.push({ stage, what })
    say(`${stage} 失败：${what} 没有返回，中止`)
    return false
  }
  return true
}
const abortWith = (stage, extra) => Object.assign(
  { aborted: stage, stage_failures: failures }, extra)

// 阶段产物清单：P8 的产物审计按这张表核对，缺一个就报一个。
const EXPECTED_DOCS = ['SPEC.md', 'LEMMAS.md', 'AUDIT.md', 'CLAIMS.md']
const OPTIONAL_DOCS = ['CITATIONS.md', 'COUNTEREXAMPLES.md', 'FORMALIZATION.md', 'FIDELITY.md']

// ── P0 陈述锁定 ────────────────────────────────────────────────────────────
phase('Spec')
const spec = await agent(
  `你是数学研究的项目负责人。工作目录：${root}。
问题：${problem}

按 WORKFLOW.md 的 P0 做陈述锁定，产出 docs/SPEC.md（用 Write 工具写文件），内容包括：
1) 对象与定义台账（每个符号：定义、定义域、正则性）；2) 编号假设 H1, H2, …，
每条注明能弱化到什么程度；3) 结论，量词写全；4) 至少三个可伪性检验族；
5) 已知的接近但不成立的例子。若问题本身模糊，在 notes 里说明并给出两种可能的精确化。
不要写证明。
**只锁定原问题本身**：不要把问题推广成更一般的结构（更一般的域/环、最优常数、n 元类比、
可变系数）。这类推广只能写进 SPEC 的「范围外」一节，且**不得进入假设或结论**——
假设写多了，下游的反例搜索会去攻击一个没人问过的问题。`,
  { label: 'spec', phase: 'Spec', schema: SPEC_SCHEMA }
)
if (!spec) {
  say('P0 失败：陈述锁定没有产出，中止（陈述没锁死，后面的证明全是白做）')
  return { aborted: 'P0', reason: 'spec agent 没有返回结果', stage_failures: failures }
}
if (!spec.hypotheses || !spec.hypotheses.length || !spec.conclusion) {
  say('P0 产出不完整：缺假设或结论，中止')
  return { aborted: 'P0', reason: 'SPEC 缺假设或结论', spec, stage_failures: failures }
}
say(`P0 完成：${spec.hypotheses.length} 条假设`)

// ── P1 文献核实 ────────────────────────────────────────────────────────────
let citations = []
if (spec && spec.needs_literature) {
  phase('Literature')
  const routes = ['arXiv 预印本', 'zbMATH / MathSciNet 条目', '期刊官网与 DOI 解析']
  const found = await parallel(
    routes.map((r) => () =>
      agent(
        `为下述问题检索文献，只走「${r}」这一路。问题：${spec.title}。
要求：每条给出 key、完整题录、可检索标识符（DOI / arXiv / zbMATH）、与本文的关系。
不确定的一律不要写。`,
        { label: `cite:${r}`, phase: 'Literature', schema: CITATIONS_SCHEMA }
      )
    )
  )
  const seen = new Set()
  const merged = []
  for (const r of found.filter(Boolean)) {
    for (const e of r.entries) {
      const k = (e.identifier || '').toLowerCase().trim()
      if (!k || seen.has(k)) continue
      seen.add(k)
      merged.push(e)
    }
  }
  const verified = await parallel(
    merged.map((e) => () =>
      agent(
        `独立复核这条文献，不要相信下面文字，去检索标识符本身：
${JSON.stringify(e)}
打开 DOI/arXiv 页面，核对标题、作者、年份、结论是否与描述一致。
一致 → VERIFIED；不一致 → REJECTED 并在 correction 里写正确题录；查不到 → REJECTED。`,
        { label: `verify:${e.key}`, phase: 'Literature', schema: VERIFY_SCHEMA }
      ).then((v) => ({ e, v }))
    )
  )
  citations = verified.filter(Boolean).filter((x) => x.v && x.v.verdict === 'VERIFIED')
  await agent(
    `把已核实文献写进 ${root}/docs/CITATIONS.md，并列出被拒绝的条目与原因。
已核实：${JSON.stringify(citations.map((c) => c.e))}
被拒：${JSON.stringify(verified.filter(Boolean).filter((x) => !x.v || x.v.verdict !== 'VERIFIED').map((x) => ({ e: x.e, why: x.v && x.v.reason })))}`,
    { label: 'citations-doc', phase: 'Literature' }
  )
  say(`P1 完成：核实 ${citations.length} 条`)
}

// ── P2 证明构造（两条独立路线）─────────────────────────────────────────────
phase('Proof')
const routes = await parallel([
  () =>
    agent(`路线 A：直接分解。问题：${spec.title}。假设：${JSON.stringify(spec.hypotheses)}。
结论：${spec.conclusion}。给出引理 DAG：每条引理有 id、陈述、证明、依赖、状态。`,
      { label: 'proof:A', phase: 'Proof', schema: LEMMAS_SCHEMA }),
  () =>
    agent(`路线 B：换一个分解（例如反证法、对偶、能量/极值原理、逼近论），不要沿用最直接的思路。
问题：${spec.title}。假设：${JSON.stringify(spec.hypotheses)}。结论：${spec.conclusion}。
给出引理 DAG。`, { label: 'proof:B', phase: 'Proof', schema: LEMMAS_SCHEMA }),
])

const proofs = routes.filter(Boolean)
let lemmas = []
if (proofs.length) {
  const picked = await agent(
    `比较两条证明路线，选一条或合并，输出最终引理 DAG（JSON）。
路线 A：${JSON.stringify(proofs[0])}
路线 B：${JSON.stringify(proofs[1] || null)}
合并要求：依赖不得成环；等价改写不算独立证明，要在 proof 里点明。`,
    { label: 'proof:merge', phase: 'Proof', schema: LEMMAS_SCHEMA }
  )
  if (!must('P2', 'proof:merge', picked)) {
    return abortWith('P2', { spec, lemmas: 0 })
  }
  lemmas = (picked && picked.lemmas) || []
  await agent(
    `把引理 DAG 写入 ${root}/docs/LEMMAS.md（表格 + 依赖图），并画出一张 ASCII 依赖图。
数据：${JSON.stringify(picked)}`,
    { label: 'lemmas-doc', phase: 'Proof' }
  )
  if (!lemmas.length) {
    say('P2 失败：合并后的引理 DAG 是空的，中止')
    return abortWith('P2', { spec, lemmas: 0, reason: '空引理 DAG' })
  }
}
say(`P2 完成：${lemmas.length} 条引理`)

// ── P3/P4 反例搜索 + 对抗审计（循环到两轮无新发现）─────────────────────────
phase('Attack')
const LENSES = [
  ['numeric', '数值与符号：对恒等式随机取值、对不等式扫参数；能符号化简就化简'],
  ['degenerate', '退化情形：零、空集、常值、一维、轴对称、周期化、紧支撑'],
  ['limits', '极限情形：分别取与联合取 t→-∞、ρ→0、R→∞、ν→0、ε→0'],
  ['quantifier', '量词与尺度：∀/∃ 顺序、lim 与 sup 交换、伸缩变换下两端是否同阶'],
]
const confirmed = []
const seenKey = new Set()
let dry = 0
let round = 0
let attackSpent = 0
let skippedFindings = 0
const SEV = { fatal: 0, major: 1, minor: 2 }
while (dry < maxRounds && round < 4 && lemmas.length && attackSpent + 4 <= attackBudget) {
  round += 1
  attackSpent += LENSES.length
  const found = await parallel(
    LENSES.map(([tag, desc]) => () =>
      agent(
        `攻击下列引理，目标是**推翻**它们。lens=${tag}：${desc}
问题：${spec.title}。引理：${JSON.stringify(lemmas)}
只报告具体的、可复现的疑点（给出反例、参数、或推导步骤），不要泛泛而谈。
没有发现就返回空数组。`,
        { label: `attack:${tag}#${round}`, phase: 'Attack', schema: FINDINGS_SCHEMA }
      )
    )
  )
  const fresh = found.filter(Boolean).flatMap((r) => r.findings)
    .filter((f) => {
      const k = `${f.target}|${f.summary}`.slice(0, 200)
      if (seenKey.has(k)) return false
      seenKey.add(k)
      return true
    })
  if (!fresh.length) { dry += 1; say(`第 ${round} 轮无新发现`); continue }
  dry = 0
  // 每轮只判最严重的若干条；被判掉的如实记下来，不许安静截断。
  fresh.sort((a, b) => (SEV[a.severity] ?? 9) - (SEV[b.severity] ?? 9))
  const affordable = Math.max(0, Math.floor((attackBudget - attackSpent) / 3))
  const keep = Math.min(maxFindingsPerRound, affordable, fresh.length)
  skippedFindings += fresh.length - keep
  const toJudge = fresh.slice(0, keep)
  if (keep < fresh.length) {
    say(`第 ${round} 轮：${fresh.length} 条新疑点，预算内只判前 ${keep} 条（跳过 ${fresh.length - keep} 条）`)
  }
  // 致命/重大意见三个 lens 独立判；minor 只判一次，别用三个 agent 换一个"措辞问题"。
  const judged = await parallel(
    toJudge.map((f) => () =>
      parallel(
        (f.severity === 'minor' ? ['复现'] : ['复现', '找反例', '查是否只是措辞']).map((lens) => () =>
          agent(
            `用「${lens}」这个角度独立判定下面这条审计意见是否成立：
${JSON.stringify(f)}
默认怀疑它是错的；能复现或能给出具体反例才判 CONFIRMED。`,
            { label: `judge:${lens}`, phase: 'Attack', schema: JUDGE_SCHEMA }
          )
        )
      ).then((votes) => ({
        f,
        confirmed: votes.filter(Boolean).filter((v) => v.verdict === 'CONFIRMED').length,
        plausible: votes.filter(Boolean).filter((v) => v.verdict === 'PLAUSIBLE').length,
        needed: f.severity === 'minor' ? 1 : 2,
      }))
    )
  )
  attackSpent += toJudge.reduce((n, f) => n + (f.severity === 'minor' ? 1 : 3), 0)
  for (const j of judged.filter(Boolean)) {
    if (j.confirmed >= (j.needed || 2)) confirmed.push(j.f)
  }
  say(`第 ${round} 轮：${fresh.length} 条新疑点，${judged.filter(Boolean).filter((j) => j.confirmed >= (j.needed || 2)).length} 条确认`)
}
if (round < 4 && dry < maxRounds && attackSpent + 4 > attackBudget) {
  say(`攻击阶段按预算停止：已用 ${attackSpent}/${attackBudget} 个 agent`)
}

await agent(
  `把审计结果写入 ${root}/docs/AUDIT.md 与 ${root}/docs/COUNTEREXAMPLES.md。
确认的问题：${JSON.stringify(confirmed)}
另需记录：每轮攻击用了哪些 lens、哪些引理被攻击过、哪些仍未被覆盖。`,
  { label: 'audit-doc', phase: 'Attack' }
)

if (confirmed.length) {
  const revised = await agent(
    `根据已确认的问题修订证明，输出修订后的引理 DAG（可改陈述、可降级为 CONDITIONAL/OPEN、
可撤回）。确认问题：${JSON.stringify(confirmed)}
原 DAG：${JSON.stringify(lemmas)}
修订规则：能修则修；修不了就降级并写明缺什么；不要为了让证明通过而削弱陈述却不标注。`,
    { label: 'proof:revise', phase: 'Attack', schema: LEMMAS_SCHEMA }
  )
  if (revised) lemmas = revised.lemmas
}
say(`P3/P4 完成：${confirmed.length} 条确认问题`)

// ── P5 形式化映射 ──────────────────────────────────────────────────────────
phase('Formalize')
const plan = await agent(
  `把每条引理映射到 Lean 4 + Mathlib。库：${lib || '待定'}，工程目录 ${root}。
引理：${JSON.stringify(lemmas)}
对每条：给出 lean_name（合法标识符）、mathlib 里可复用的声明（若不确定就写 none，不要编）、
努力程度 easy/medium/hard/not-feasible、以及需要新增的定义。
not-feasible 必须写明缺什么。写进 ${root}/docs/FORMALIZATION.md。
**定义域与假设必须和 SPEC 逐字一致**：不要为了好证而把 ℝ 放大成"任意线性有序交换环"，
也不要加 SPEC 没有的侧条件——放大定义域会让 P7 判 STRONGER，等于换了个命题来证。`,
  { label: 'formalize-plan', phase: 'Formalize', schema: FORMAL_SCHEMA }
)
if (!must('P5', 'formalize-plan', plan)) {
  return abortWith('P5', {
    spec, lemmas: lemmas.length, confirmed_findings: confirmed,
    attack_skipped: skippedFindings,
  })
}
const items = plan.items || []
const buildable = items.filter((i) => i.effort !== 'not-feasible')
if (!items.length) {
  say('P5 失败：形式化映射是空的，没有引理可以进 Lean，中止')
  return abortWith('P5', {
    spec, lemmas: lemmas.length, confirmed_findings: confirmed, reason: '空形式化映射',
  })
}
say(`P5 完成：${buildable.length}/${items.length} 条可形式化`)

// ── P6 Lean 实现（按依赖顺序，逐条编译）────────────────────────────────────
phase('Lean')
const done = new Set()
const failed = []
const attempts = {}
let pending = buildable.slice()
let guard = 0
while (pending.length && guard < 40) {
  guard += 1
  const idSet = new Set(pending.map((p) => p.id))
  const ready = pending.filter((p) => {
    const lm = lemmas.find((l) => l.id === p.id)
    return !lm || lm.deps.every((d) => done.has(d) || !idSet.has(d))
  })
  if (!ready.length) {
    // 依赖死锁：再按"随便挑三条"重试只会把剩下的引理反复打两遍，最后报一句
    // "依赖顺序卡住"了事。这里直接点名，谁被谁卡住。
    const blocked = pending.map((p) => {
      const lm = lemmas.find((l) => l.id === p.id)
      const unmet = (lm ? lm.deps : []).filter((d) => !done.has(d))
      return { id: p.id, reason: `依赖未完成：${unmet.join(', ') || '(依赖既没成功也不在待办)'}` }
    })
    failed.push(...blocked)
    say(`Lean 依赖死锁：${blocked.length} 条引理无法推进，停止（不会空转重试）`)
    pending = []
    break
  }
  const batch = ready.slice(0, 3)
  const results = await parallel(
    batch.map((p) => () => {
      const lm = lemmas.find((l) => l.id === p.id)
      return agent(
        `在 ${root} 实现这一条 Lean 引理并让它通过编译。
引理 id=${p.id}，Lean 名 ${p.lean_name}。
非形式陈述：${lm ? lm.statement : ''}
证明：${lm ? lm.proof : ''}
要求：不得使用 sorry/admit；不得新增 axiom；定义与 SPEC 的台账逐字一致。
写完运行：bash scripts/check.sh（或 lake build）；编译失败就修到通过。
如果这条引理其实证不出来，不要硬编——直接 status=FAIL 并写清卡在哪一步，它会退回证明阶段。
status=OK 的判据只有一条：该声明在源码里存在、#print axioms 只依赖白名单、scripts/check.sh 跑出 OK。`,
        { label: `lean:${p.id}`, phase: 'Lean', schema: LEAN_SCHEMA }
      ).then((r) => ({ p, r }))
    })
  )
  // 按 id 而不是按对象引用从 pending 里摘除：引用相等的假设在运行时不一定成立，
  // 而按 id 摘除无论对象是否被复制都正确。
  const got = results.filter(Boolean).map((x) => ({
    id: x.p.id, ok: !!(x.r && x.r.status === 'OK'),
    why: x.r ? (x.r.detail || '') : 'agent 没有返回',
  }))
  for (const g of got) {
    if (g.ok) {
      done.add(g.id)
      pending = pending.filter((q) => q.id !== g.id)
      continue
    }
    attempts[g.id] = (attempts[g.id] || 0) + 1
    if (attempts[g.id] >= 2) {
      failed.push({ id: g.id, reason: String(g.why).trim().slice(0, 400) })
      pending = pending.filter((q) => q.id !== g.id)
    }
  }
  say(`Lean 进度 ${done.size}/${buildable.length}，本批 ${got.filter((g) => g.ok).length}/${got.length} 通过，待办 ${pending.length}${failed.length ? `，放弃 ${failed.length}` : ''}`)
}
if (pending.length) {
  failed.push({ id: '<未处理>', reason: `达到尝试上限仍未完成：${pending.map((p) => p.id).join(', ')}` })
}
if (buildable.length && !done.size) {
  failures.push({ stage: 'P6', what: '没有任何一条引理通过 Lean 编译' })
  say('P6 失败：0 条引理通过，继续跑保真审计也只能审个空工程')
}

// ── P7 陈述保真审计 ────────────────────────────────────────────────────────
phase('Fidelity')
const fidelity = await agent(
  `你没参与形式化。逐条比对 ${root}/docs/SPEC.md 与 Lean 源码，判定每个 Lean 定理陈述
是否忠实于非形式陈述。引理与 Lean 名：${JSON.stringify(buildable)}
逐条检查：假设集合（多了=WEAKER，少了=STRONGER）、量词顺序、定义（系数与定义域）、
退化情形是否被静默排除。写进 ${root}/docs/FIDELITY.md。`,
  { label: 'fidelity', phase: 'Fidelity', schema: FIDELITY_SCHEMA }
)
if (!must('P7', 'fidelity', fidelity)) {
  return abortWith('P7', {
    spec, lemmas: lemmas.length, formalized: done.size, lean_failed: failed,
  })
}
const bad = (fidelity.items || []).filter((i) => i.verdict === 'DIFFERENT' || i.verdict === 'STRONGER')
say(`P7 完成：${bad.length} 条需要回炉`)

// ── P8/P9 台账、成文、终检 ─────────────────────────────────────────────────
phase('Writeup')

// 写文件的 agent 说"我写了"不算数：另起一个 agent 去磁盘上核。
const artifacts = await agent(
  `产物审计。不要相信任何"我已经写好了"的说法——用 Bash（ls、wc -c、head）去看磁盘。
目录：${root}/docs 与 ${root}/${lib || '（库目录）'}。
必须存在：${EXPECTED_DOCS.join('、')}；可选：${OPTIONAL_DOCS.join('、')}。
逐个返回路径、字节数、是否只有标题（empty）。missing 列应该存在但没有的，
empty 列存在但实质为空的。不要修改任何文件。`,
  { label: 'artifacts', phase: 'Writeup', schema: ARTIFACT_SCHEMA }
)
if (!artifacts) {
  failures.push({ stage: 'P8', what: 'artifacts 产物审计没有返回' })
  say('P8 警告：产物审计没跑成，本轮无法确认 docs/ 是否真的写出来了')
} else if (artifacts.missing.length || artifacts.empty.length) {
  say(`产物审计：缺 ${artifacts.missing.length} 个，空 ${artifacts.empty.length} 个`)
} else {
  say('产物审计：齐全')
}

const writeup = await agent(
  `汇总成 ${root}/docs/CLAIMS.md 台账、${root}/docs/FINAL.md 终检报告，
以及 ${root}/docs/RUNS/ 下的一份运行记录（文件名用 \`date -u +%Y%m%dT%H%M%SZ\` 生成，后缀 .json）。
引理（含状态）：${JSON.stringify(lemmas)}
形式化映射：${JSON.stringify(items)}
没能形式化的引理（要如实写进台账，不许标 PROVED）：${JSON.stringify(failed)}
保真审计：${JSON.stringify(fidelity)}
产物审计：${JSON.stringify(artifacts)}
确认的审计问题：${JSON.stringify(confirmed)}
台账规则：状态只能是 PROVED / PROVED-INFORMAL / CONDITIONAL / OPEN / REFUTED / INFORMAL-ONLY；
PROVED 必须填 lean 名且该名出现在 Audit.lean；CONDITIONAL 必须写清假设；
REFUTED 必须写反例；INFORMAL-ONLY 单独标注。
终检清单按 WORKFLOW.md 第 9 节逐条打勾，未通过项写明原因。
运行记录里写：问题陈述、每阶段产物、引理数、确认问题、被降级/撤回的条目、产物审计结果。
**终检里记下的偏差要真的改掉**：如果 FORMALIZATION.md / LEMMAS.md / AUDIT.md 里的状态与
最终源码不一致（比如还写着"待落库"），直接更正那几张表——只在终检里记一笔、留在原地不管，
下一个读文档的人看到的就是错的。
不要美化结果：没证出来的就写没证出来。`,
  { label: 'ledger', phase: 'Writeup' }
)

if (!writeup) {
  failures.push({ stage: 'P9', what: 'writeup 没有返回，台账/终检/运行记录都没写' })
  say('P9 失败：台账与运行记录没有落盘，本次运行不算完成')
}

return {
  ok: failures.length === 0,
  stage_failures: failures,
  spec,
  lemmas: lemmas.length,
  citations: citations.length,
  attack_skipped: skippedFindings,
  confirmed_findings: confirmed,
  formalized: done.size,
  lean_failed: failed,
  not_feasible: items.filter((i) => i.effort === 'not-feasible').map((i) => i.id),
  fidelity_flags: bad,
  artifacts: artifacts
    ? { missing: artifacts.missing, empty: artifacts.empty }
    : { missing: ['<产物审计未返回>'], empty: [] },
  summary: writeup,
}
