/-
Step 4 (B), part 2 (bergdb 024-22; 024-12's (4)): a merge adds at most one to
the heights. Its new nodes have the merged node's height; its parent, the
path's node above it, takes them in place or by a split whose cascade goes up
the path (`sb_mergeParent`, `sb_merge`, `seenHeight_merge`).
-/
import SIS.Tree.HeightsFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

end SIS.Tree
