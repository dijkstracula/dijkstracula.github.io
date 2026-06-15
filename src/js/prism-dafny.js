// Dafny syntax highlighting for Prism.js
(function (Prism) {
  Prism.languages.dafny = {
    'comment': [
      {
        // Block comments /* ... */
        pattern: /\/\*[\s\S]*?\*\//,
        greedy: true
      },
      {
        // Line comments //
        pattern: /\/\/.*$/m,
        greedy: true
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

    // Attributes like {:axiom}, {:trigger foo}, {:fuel f, 1}
    'attribute': {
      pattern: /\{:[a-zA-Z_][a-zA-Z0-9_]*(?:\s+[^}]*)?\}/,
      greedy: true
    },

    // Spec / verification keywords — Hoare-logic-flavored
    // Distinguished as 'builtin' so they can be styled distinctly from
    // ordinary control-flow / declaration keywords.
    'builtin': /\b(?:requires|ensures|invariant|decreases|modifies|reads|yields|assert|assume|calc|forall|exists|by|witness|reveal|hide|fresh|old)\b/,

    // Declaration, control-flow, and modifier keywords
    'keyword': /\b(?:method|function|predicate|lemma|ghost|twostate|var|const|return|returns|yield|new|null|this|class|datatype|codatatype|trait|type|newtype|iterator|module|import|include|opened|refines|abstract|extends|export|provides|if|then|else|while|for|match|case|do|in|let|opaque|static|protected|nameonly|label|pure|break|continue|print)\b/,

    // Types and capitalized identifiers (likely user-defined types/constructors)
    'class-name': [
      {
        pattern: /\b(?:int|nat|real|bool|char|string|seq|set|iset|multiset|map|imap|array|array2|array3|object|Type)\b/,
        alias: 'type'
      },
      {
        pattern: /\b[A-Z][a-zA-Z0-9_]*/,
        alias: 'type'
      }
    ],

    // Boolean and null literals
    'boolean': /\b(?:true|false|null)\b/,

    // Numbers (hex, binary, decimal, real)
    'number': /\b(?:0x[0-9a-fA-F]+|0b[01]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\b/,

    // Operators — order matters: longer patterns must come first.
    // Note: !in needs a word boundary so it doesn't match !ineligible etc.
    'operator': /<==>|==>|<==|=>|!in\b|>=|<=|==|!=|&&|\|\||::|:=|\.\.|[+\-*\/%<>=!|&]/,

    // Punctuation
    'punctuation': /[{}[\]();,.:]/
  };

  // Aliases for common file extensions / fence labels
  Prism.languages.dfy = Prism.languages.dafny;
}(Prism));
