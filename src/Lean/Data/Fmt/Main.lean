/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Environment
public import Lean.Data.Fmt.Error
import Lean.Data.Fmt.FmtM
import Std.Data.HashMap.AdditionalOperations
import Lean.Data.Fmt.Comments
import Lean.Data.Fmt.Formatter

namespace Lean.Fmt

def filterRawFormattedComments
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (rawFormattedTokens : Std.HashMap Syntax.Range RawFormattedToken) :
    Std.HashMap Syntax.Range (Array Comment) :=
  let comments := comments.map fun _ cs =>
    cs.filter fun c => Id.run do
      let some rawFormattedToken := rawFormattedTokens.get? c.originalTokenRange
        | return true
      let some formattedTrailingRange := rawFormattedToken.formattedTrailingRange?
        | return true
      return ! formattedTrailingRange.includes c.originalTrailingRange
  comments.filter fun _ cs => ! cs.isEmpty

/--
Associates all syntax ranges that have been tagged by `Fmt.fmt` with the portions of the rendered
string that a specific tagged sub-document has been rendered to.
Tagged syntax ranges that do not appear in the rendered string at all are removed.
-/
def connectTags
    {rendering : String.Slice}
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId))
    (tagsToRendered : Std.HashMap TagId (Std.HashSet rendering.Subslice)) :
    Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice) :=
  -- 1. All `TagId`s in `tagsToRendered` are contained in `syntaxToTags`.
  -- 2. Only `Syntax.Range`s that have been assigned by the document construction will appear in
  --   `syntaxToTags`. This includes `Syntax` subtrees for which `Fmt.fmt` has been called,
  --   as well as all tokens that appear in the constructed document for which `Fmt.text` has been
  --   called.
  -- 3. `TagId`s in `syntaxToTags` that are not used in the specific alternative chosen by the
  --   formatter do not appear in `tagsToRendered`.
  -- 4. Multiple `TagId`s are associated with the same `Syntax.Range` in `syntaxToTags` when
  --    `Fmt.fmt` is called for a `Syntax` subtree that contains another `Syntax` subtree of the
  --    same range for which `Fmt.fmt` has also been called.
  -- 5. Multiple `rendering.Subslice`s are associated with the same `TagId` in `tagsToRendered` when
  --    a sub-document is shared in multiple places in the same alternative,
  --    e.g. when a formatter yields the same document twice for the same token in the
  --    input `Syntax`.
  syntaxToTags.filterMap fun _ tags => do
    let mut ranges := {}
    for tag in tags do
      if let some rendered := tagsToRendered.get? tag then
        ranges := ranges.insertMany rendered
    guard <| ! ranges.isEmpty
    return ranges

public def main (env : Environment) (opts : Options) (stx : Syntax) : Except Error String := do
  let lineInfos := collectSyntaxLineInfos stx
  let comments ← collectComments stx
  let (taggedDoc, syntaxToTags, rawFormattedTokens) ← FmtM.run env opts lineInfos <| fmt stx
  let comments := filterRawFormattedComments comments rawFormattedTokens
  let doc := taggedDoc.doc
  let some output := format? doc 100
    | throw <| .formattingFailure stx doc
  let tagsToRendered := output.tags
  let syntaxToRendered := connectTags syntaxToTags tagsToRendered
  let rendering := insertComments 100 output.rendering syntaxToRendered comments
  return rendering
