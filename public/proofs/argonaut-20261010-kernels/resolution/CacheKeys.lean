import Cache.Hashing

open Cache Cache.IO Cache.Hashing Lean in
def main : IO Unit := CacheM.run do
  let memo ← getHashMemo {}
  for (mod, key) in memo.hashMap.toArray do
    IO.println s!"{mod}\t{key.asLTar}"
