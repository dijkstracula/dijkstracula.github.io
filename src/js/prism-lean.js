// Lean 4 syntax highlighting for Prism.js
(function (Prism) {
  Prism.languages.lean = {
    'comment': [
      {
        // Block comments /- ... -/
        pattern: /\/-[\s\S]*?-\//,
        greedy: true
      },
      {
        // Line comments --
        pattern: /--.*$/m,
        greedy: true
      },
      {
        // Doc comments /-- ... -/
        pattern: /\/--[\s\S]*?-\//,
        greedy: true,
        alias: 'doc-comment'
      }
    ],
    'string': {
      pattern: /"(?:[^"\\]|\\.)*"/,
      greedy: true
    },
    'char': {
      pattern: /'(?:[^'\\]|\\.)'/,
      greedy: true
    },

    // Keywords and important constructs
    'keyword': /\b(?:def|theorem|lemma|example|axiom|inductive|structure|class|instance|deriving|extends|where|variable|universe|opaque|abbrev|open|import|export|namespace|section|end|mutual|partial|unsafe|protected|private|noncomputable|macro|syntax|notation|infix|infixl|infixr|prefix|postfix|if|then|else|match|with|do|let|in|have|show|suffices|from|fun|λ|by|calc|at|nomatch)\b/,

    // Tactics (commonly used in proofs)
    'builtin': /\b(?:intro|intros|apply|exact|refine|rfl|simp|simp_all|rw|rewrite|induction|cases|split|constructor|left|right|exists|use|assumption|contradiction|sorry|admit|done|trivial|ring|omega|linarith|norm_num|decide|unfold|conv|repeat|try|all_goals|any_goals|focus|skip)\b/,

    // Types and type-related keywords
    'class-name': [
      {
        pattern: /\b(?:Type|Prop|Sort|Nat|Int|String|Char|Bool|List|Array|Option|Sum|Prod|Unit|Empty|True|False|Eq|Ne|And|Or|Not|Exists|Forall)\b/,
        alias: 'type'
      },
      {
        // Capitalized identifiers (likely types/constructors)
        pattern: /\b[A-Z][a-zA-Z0-9_']*/,
        alias: 'type'
      }
    ],

    // Boolean and special values
    'boolean': /\b(?:true|false|none|some)\b/,

    // Numbers
    'number': /\b(?:0x[0-9a-fA-F]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\b/,

    // Operators
    'operator': /[+\-*\/%=<>!&|^~:]+|\.{2,3}|@\[|#\[|\||→|←|↔|∀|∃|λ|≠|≤|≥|∧|∨|¬|⊢|⊨/,

    // Punctuation
    'punctuation': /[{}[\]();,.:]/,

    // Attributes
    'attribute': /@\[[^\]]*\]|#\[[^\]]*\]/
  };

  // Alias
  Prism.languages.lean4 = Prism.languages.lean;
}(Prism));
