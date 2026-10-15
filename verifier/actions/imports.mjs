// Read Lean import declarations as data.
export function leanImports(source) {
  let clean = "",
    depth = 0,
    quoted = false;
  for (let i = 0; i < source.length; i++) {
    const pair = source.slice(i, i + 2),
      ch = source[i];
    if (depth) {
      if (pair === "/-") {
        depth++;
        i++;
        clean += "  ";
      } else if (pair === "-/") {
        depth--;
        i++;
        clean += "  ";
      } else clean += ch === "\n" ? "\n" : " ";
    } else if (quoted) {
      if (ch === "\\") {
        i++;
        clean += "  ";
      } else {
        if (ch === '"') quoted = false;
        clean += ch === "\n" ? "\n" : " ";
      }
    } else if (pair === "/-") {
      depth++;
      i++;
      clean += "  ";
    } else if (pair === "--") {
      while (i < source.length && source[i] !== "\n") {
        clean += " ";
        i++;
      }
      clean += "\n";
    } else if (ch === '"') {
      quoted = true;
      clean += " ";
    } else clean += ch;
  }
  const result = new Set();
  for (const match of clean.matchAll(
    /^[ \t]*(?:(?:public|meta|private)[ \t]+)*import\s+([A-Z][A-Za-z0-9_.]*(?:\s+[A-Z][A-Za-z0-9_.]*)*)/gm,
  ))
    for (const name of match[1].trim().split(/\s+/))
      if (/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(name))
        result.add(name);
  return [...result].sort();
}
