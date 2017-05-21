--
-- Filename: RedBlackTree.idr
-- Path: benbu-q
-- Created Date: Thu May 11 2017
-- Author: t-rel
-- 
-- Copyright (c) 2017 Microsoft
--

||| An implementation of red-black trees, using Idris' type system to enforce
||| tree balance.
||| References:
|||  - http://adam.chlipala.net/cpdt/html/MoreDep.html
|||  - https://github.com/lives-group/red-black-trees-agda (A more formal ver)
|||  - https://fstaals.net/RedBlackTree.html (Some code is ported from this 
|||    Haskell implementation)
|||
|||
module Data.Dict.RedBlackTree

-- YY8YY 0   0 8YYYo 8YYYY oYYYo 
--   0   "o o" 8___P 8___  %___  
--   0     0   8"""  8"""  `"""p 
--   0     0   0     8oooo YoooY 

||| Define the type of the colors
data Color = Red | Black

||| Define the type of red-black tree node.
|||
|||    Color   Black Height   Element Type
|||         \         |        /
data Node : Color -> Nat -> Type -> Type where
	||| Every leaf is black (and has black height 0).
	Leaf  : Node Black Z a
	||| The black height left and right is the same.
	||| Adding a black node increases the black height.
	NodeB : Node lc    h a -> a -> Node rc    h a -> Node Black (S h) a
	||| If a node is red, its children must be black.
	NodeR : Node Black h a -> a -> Node Black h a -> Node Red   h a

||| A top-level wrapper for RBT.
export
data RedBlackTree : Type -> Type where
	||| A red-black-tree's root node is always black.
	Tree : Node Black h a -> RedBlackTree a

||| Creating an empty tree.
export
empty : RedBlackTree a
empty = Tree Leaf

-- Y8Y 8o  0 oYYYo 8YYYY 8YYYo YY8YY Y8Y _YYY_ 8o  0 
--  0  8Yo 8 %___  8___  8___P   0    0  0   0 8Yo 8 
--  0  8 Yo8 `"""p 8"""  8""Yo   0    0  0   0 8 Yo8 
-- o8o 0   8 YoooY 8oooo 0   0   0   o8o "ooo" 0   8 

||| Result of inserting one node to a black-rooted subtree:
data BlackInsertResult : Nat -> Type -> Type where
	||| After inserting to a black-rooted subtree, the root is still black.
	BDone  : Node Black h a -> BlackInsertResult h a
	||| After inserting to a black-rooted subtree, the root turned into red.
	NewRed : Node Red   h a -> BlackInsertResult h a

||| The red-red secanrio described below.
data RedRed : Nat -> Type -> Type where
	||| Left branch is red
	LeftR  : Node Red   h a -> a -> Node Black h a -> RedRed h a
	||| Right branch is red
	RightR : Node Black h a -> a -> Node Red   h a -> RedRed h a

||| Result of inserting one node to a red-rooted subtree:
data RedInsertResult : Nat -> Type -> Type where
	||| The children are still all black.
	RDone  : Node Red   h a -> RedInsertResult h a
	||| Some children is tainted into red, breaking invariant.
	MadeRR : RedRed     h a -> RedInsertResult h a

||| Insertion result of some node with color we do not know.
||| So we have to keep the possibilities.
data InsertResult : Nat -> Type -> Type where
	InsertR : RedInsertResult   h a -> InsertResult h a
	InsertB : BlackInsertResult h a -> InsertResult h a

||| Balancing a red<-red<-X secanrio.
balanceL : RedRed h a -> a -> Node c h a -> Node Red (S h) a
balanceL (LeftR (NodeR lll llx llr) lx lr)  x r = do
	let l' = NodeB lll llx llr
	let r' = NodeB lr  x   r
	NodeR l' lx r'
balanceL (RightR ll lx (NodeR lrl lrx lrr)) x r = do
	let l' = NodeB ll  lx   lrl
	let r' = NodeB lrr x    r
	NodeR l' lrx r'

||| Balancing a X->red->red secanrio.
balanceR : Node c h a -> a -> RedRed h a -> Node Red (S h) a
balanceR l x (LeftR (NodeR rll rlx rlr) rx rr)  = do
	let l' = NodeB l   x   rll
	let r' = NodeB rlr rx  rr
	NodeR l' rlx r'
balanceR l x (RightR rl rx (NodeR rrl rrx rrr)) = do
	let l' = NodeB l   x    rl
	let r' = NodeB rrl rrx  rrr
	NodeR l' rx r'

mutual
	||| Inserting into a node with arbitrary color
	insertUnder : Ord a => a -> Node c h a -> InsertResult h a
	insertUnder x n = case n of
		Leaf        => InsertB $ insertLeaf x n
		NodeB _ _ _ => InsertB $ insertBlack x n
		NodeR _ _ _ => InsertR $ insertRed x n

	||| Inserting something in a leaf creates a new red node. 
	||| Furthermore, note that leaves specifically have black height zero.
	insertLeaf : a -> Node Black Z a -> BlackInsertResult Z a
	insertLeaf x Leaf = NewRed $ NodeR Leaf x Leaf

	||| Inserting into a red-rooted subtree
	insertRed : Ord a => a -> Node Red h a -> RedInsertResult h a
	insertRed x (NodeR l y r) with (x <= y)
		| True with (insertBlack x l)
			| BDone l'  = RDone  $ NodeR l' y r -- Good, nothing special happens
			| NewRed l' = MadeRR $ LeftR l' y r -- Oh, we made a red-red
		| False with (insertBlack x r)
			| BDone r'  = RDone  $ NodeR  l y r' -- Good, nothing special happens
			| NewRed r' = MadeRR $ RightR l y r' -- Oh, we made a red-red
	
	||| Inserting into a black-rooted subtree
	insertBlack : Ord a => a -> Node Black h a -> BlackInsertResult h a
	insertBlack x Leaf = insertLeaf x Leaf
	insertBlack x (NodeB l y r) with (x <= y)
		| True with (insertUnder x l)
			| InsertB (BDone  l') = BDone  $ NodeB    l' y r
			| InsertB (NewRed l') = BDone  $ NodeB    l' y r
			| InsertR (RDone  l') = BDone  $ NodeB    l' y r
			| InsertR (MadeRR l') = NewRed $ balanceL l' y r -- We need to balance
		| False with (insertUnder x r)
			| InsertB (BDone  r') = BDone  $ NodeB    l  y r'
			| InsertB (NewRed r') = BDone  $ NodeB    l  y r'
			| InsertR (RDone  r') = BDone  $ NodeB    l  y r'
			| InsertR (MadeRR r') = NewRed $ balanceR l  y r' -- We need to balance

||| Turn a red node into black, with increased height.
turnBlack : Node Red h a -> Node Black (S h) a
turnBlack (NodeR l x r) = NodeB l x r

export
insert : Ord a => a -> RedBlackTree a -> RedBlackTree a
insert x (Tree n) with (insertBlack x n)
	| BDone  bn = Tree bn
	| NewRed rn = Tree $ turnBlack rn

export
insertAll : Ord a => List a -> RedBlackTree a -> RedBlackTree a
insertAll = flip (foldr insert)

export
fromList : Ord a => List a -> RedBlackTree a
fromList xs = insertAll xs empty

-- 8888_ 8YYYY 0    8YYYY YY8YY Y8Y _YYY_ 8o  0 
-- 0   0 8___  0    8___    0    0  0   0 8Yo 8 
-- 0   0 8"""  0    8"""    0    0  0   0 8 Yo8 
-- 8oooY 8oooo 8ooo 8oooo   0   o8o "ooo" 0   8 

||| Results of deleting a child under a red node
||| A wrapper of the red node.
data RedDeleteResult : Nat -> Type -> Type where
	-- Nothing special happened
	RDeleted : Node Red   h a -> RedDeleteResult h a
	-- Used recoloring to maintain tree height
	NewBlack : Node Black h a -> RedDeleteResult h a

||| Results of deleting a child under a black node
||| A wrapper of the black node.
data BlackDeleteResult : Nat -> Type -> Type where
	-- Nothing special happened
	BDeleted : Node Black h a -> BlackDeleteResult h a
	-- Tree height reduced during deletion. Note the type signature
	BShallow : Node Black h a -> BlackDeleteResult (S h) a

||| Balancing under deletion
redBalanceL : Node Black h a -> a -> Node Black (S h) a -> RedDeleteResult (S h) a
redBalanceL l x (NodeB rl rx rr) with (rl)
	| Leaf        = let l' = NodeR l x rl in
					NewBlack $ NodeB l' rx rr
	| NodeB _ _ _ = let l' = NodeR l x rl in
					NewBlack $ NodeB l' rx rr
	| NodeR _ _ _ = let l' = RightR   l x rl in
					RDeleted $ balanceL l' rx rr

redBalanceR : Node Black (S h) a -> a -> Node Black h a -> RedDeleteResult (S h) a
redBalanceR (NodeB ll lx lr) x r with (lr)
	| Leaf        = let r' = NodeR lr x r in
					NewBlack $ NodeB ll lx r'
	| NodeB _ _ _ = let r' = NodeR lr x r in
					NewBlack $ NodeB ll lx r'
	| NodeR _ _ _ = let r' = LeftR lr x r in
					RDeleted $ balanceR ll lx r'

blackBalanceR : Node c (S h) a -> a -> Node Black h a -> BlackDeleteResult (S (S h)) a
blackBalanceR (NodeB ll lx lr) x r with (lr)
	| Leaf        = let r' = NodeR lr x r
					in BShallow $ NodeB ll lx r'
	| NodeB _ _ _ = let r' = NodeR lr x r
					in BShallow $ NodeB ll lx r'
	| NodeR _ _ _ = do
		let r' = LeftR lr x r
		let t  = balanceR ll lx r'
		BDeleted $ turnBlack t
blackBalanceR (NodeR ll lx (NodeB lrl lrx lrr)) x r with (lrr)
	| Leaf = do
		let rr' = NodeR lrr x r
		let r' = NodeB lrl lrx rr'
		BDeleted $ NodeB ll lx r'
	| NodeB _ _ _ =  do
		let rr' = NodeR lrr x r
		let r' = NodeB lrl lrx rr'
		BDeleted $ NodeB ll lx r'
	| NodeR _ _ _ = do
		let rr' = LeftR lrr x r
		let r'  = balanceR lrl lrx rr'
		BDeleted $ NodeB ll lx r'

blackBalanceL : Node Black h a -> a -> Node c (S h) a -> BlackDeleteResult (S (S h)) a
blackBalanceL l x (NodeB rl rx rr) with (rl)
	| Leaf        = let l' = NodeR l x rl
					in BShallow $ NodeB l' rx rr
	| NodeB _ _ _ = let l' = NodeR l x rl
					in BShallow $ NodeB l' rx rr
	| NodeR _ _ _ = do
		let l' = RightR l x rl
		let t  = balanceL l' rx rr
		BDeleted $ turnBlack t
blackBalanceL l x (NodeR (NodeB rll rlx rlr) rx rr) with (rll)
	| Leaf        = do
		let ll' = NodeR l x rll
		let l'  = NodeB ll' rlx rlr
		BDeleted $ NodeB l' rx rr
	| NodeB _ _ _ = do
		let ll' = NodeR l x rll
		let l'  = NodeB ll' rlx rlr
		BDeleted $ NodeB l' rx rr
	| NodeR _ _ _ = do
		let ll' = RightR l x rll
		let l'  = balanceL ll' rlx rlr
		BDeleted $ NodeB l' rx rr

||| Deletion operations
||| These six functions constructs a deletion result based on a deletion result
||| of a subtree and its unchanged half. The valid color/direction branches are
||| six.
redDeleteLeft : BlackDeleteResult h a -> a -> Node Black h a -> RedDeleteResult h a
redDeleteLeft (BDeleted l) x r = RDeleted $ NodeR l x r
redDeleteLeft (BShallow l) x r = redBalanceL      l x r -- need balance

redDeleteRight : Node Black h a -> a -> BlackDeleteResult h a -> RedDeleteResult h a
redDeleteRight l x (BDeleted r) = RDeleted $ NodeR l x r
redDeleteRight l x (BShallow r) = redBalanceR      l x r -- need balance

blackDeleteLeftB : BlackDeleteResult h a -> a -> Node rc h a -> BlackDeleteResult (S h) a
blackDeleteLeftB (BDeleted l) x r = BDeleted $ NodeB l x r
blackDeleteLeftB (BShallow l) x r = blackBalanceL    l x r-- need balance

blackDeleteLeftR : RedDeleteResult h a -> a -> Node rc h a -> BlackDeleteResult (S h) a
blackDeleteLeftR (RDeleted l) x r = BDeleted $ NodeB l x r
blackDeleteLeftR (NewBlack l) x r = BDeleted $ NodeB l x r

blackDeleteRightB : Node rc h a -> a -> BlackDeleteResult h a -> BlackDeleteResult (S h) a
blackDeleteRightB l x (BDeleted r) = BDeleted $ NodeB l x r
blackDeleteRightB l x (BShallow r) = blackBalanceR    l x r -- need balance

blackDeleteRightR : Node rc h a -> a -> RedDeleteResult h a -> BlackDeleteResult (S h) a
blackDeleteRightR l x (RDeleted r) = BDeleted $ NodeB l x r
blackDeleteRightR l x (NewBlack r) = BDeleted $ NodeB l x r

mutual
	||| Extract minimal element under a black node.
	extractMinB : Node Black (S h) a -> (a, BlackDeleteResult (S h) a)
	extractMinB (NodeB Leaf x r) with (r)
		| Leaf        = (x, BShallow r)
		| NodeR _ _ _ = (x, BDeleted $ turnBlack r)
	extractMinB (NodeB l x r) with (l)
		| NodeB _ _ _ = do
			let (m, l') = extractMinB l
			(m, blackDeleteLeftB l' x r)
		| NodeR _ _ _ = do
			let (m, l') = extractMinR l
			(m, blackDeleteLeftR l' x r)
	
	||| Extract minimal element under a red node.
	extractMinR : Node Red h a -> (a, RedDeleteResult h a)
	extractMinR (NodeR Leaf x r) = (x, NewBlack r)
	extractMinR (NodeR l x r) with (l)
		| NodeB _ _ _ = do
			let (m, l') = extractMinB l
			(m, redDeleteLeft l' x r)

mutual
	||| Delete a node under a red node.
	deleteR : Ord a => a -> Node Red h a -> RedDeleteResult h a
	deleteR x (NodeR l y r) with (compare x y)
		| EQ = case (l, r) of
			(Leaf, Leaf) => NewBlack Leaf
			(_, NodeB _ _ _) => let (m, r') = extractMinB r in
				redDeleteRight l m r'
		| LT = redDeleteLeft  (deleteB x l) y r
		| GT = redDeleteRight l y (deleteB x r)

	||| Delete a node under a black node.
	deleteB : Ord a => a -> Node Black h a -> BlackDeleteResult h a
	deleteB _ Leaf          = BDeleted $ Leaf
	deleteB x (NodeB l y r) with (compare x y)
		| EQ with ((l, r))
			| (Leaf, Leaf) = BShallow Leaf
			| (Leaf, NodeR Leaf z Leaf) = BDeleted $ NodeB Leaf z Leaf
			| (NodeR Leaf z Leaf, Leaf) = BDeleted $ NodeB Leaf z Leaf
			| (_, NodeR _ _ _) = do
				let (m,r') = extractMinR r
				blackDeleteRightR l m r'
			| (_, NodeB _ _ _) = do
				let (m,r') = extractMinB r
				blackDeleteRightB l m r'
			| _ = assert_unreachable
		| LT with (l)
			| Leaf        = blackDeleteLeftB (deleteB x l) y r
			| NodeB _ _ _ = blackDeleteLeftB (deleteB x l) y r
			| NodeR _ _ _ = blackDeleteLeftR (deleteR x l) y r
		| GT with (r)
			| Leaf        = blackDeleteRightB l y (deleteB x r)
			| NodeB _ _ _ = blackDeleteRightB l y (deleteB x r)
			| NodeR _ _ _ = blackDeleteRightR l y (deleteR x r)

||| Overall Deletion
export
delete : Ord a => a -> RedBlackTree a -> RedBlackTree a
delete x (Tree bn) = case deleteB x bn of
	BDeleted bn' => Tree bn'
	BShallow bn' => Tree bn'

-- 0    _YYY_ _YYY_ 0  oY 0   0 8YYYo 
-- 0    0   0 0   0 8_oY  0   0 8___P 
-- 0    0   0 0   0 8"Yo  0   0 8"""  
-- 8ooo "ooo" "ooo" 0  Yo "ooo" 0     

||| Find the minimal element that is larger than request.
export
lookupGTE : Ord a => a -> RedBlackTree a -> Maybe a
lookupGTE x (Tree bn) = lookupNode x bn
where
	lookupNode : Ord a => a -> Node c h a -> Maybe a
	lookupBranch : Ord a => a -> Node cl h a -> a -> Node cr h a -> Maybe a
	lookupNode x Leaf = Nothing
	lookupNode x (NodeR l y r) = lookupBranch x l y r
	lookupNode x (NodeB l y r) = lookupBranch x l y r

	lookupBranch x l y r with (compare x y)
		| EQ = Just x
		| GT = lookupNode x r
		| LT with (lookupNode x l)
			| Nothing = Just y
			| Just y' = Just y'

||| Find an exact.
export
lookup : Ord a => a -> RedBlackTree a -> Maybe a
lookup x t with (lookupGTE x t)
	| Nothing = Nothing
	| Just y = if (x == y) then (Just x) else Nothing


-- 8YYYY 0   0 8o  0  oYYo YY8YY _YYY_ 8YYYo 
-- 8___  0   0 8Yo 8 0   "   0   0   0 8___P 
-- 8"""  0   0 8 Yo8 0   ,   0   0   0 8""Yo 
-- 0     "ooo" 0   8  YooY   0   "ooo" 0   0 

Functor (Node c h) where
	map f Leaf = Leaf
	map f (NodeB l x r) = NodeB (map f l) (f x) (map f r)
	map f (NodeR l x r) = NodeR (map f l) (f x) (map f r)

export
Functor RedBlackTree where
	map f (Tree t) = Tree (map f t)

-- 8YYYY _YYY_ 0    8888_  o8o  8888. 0    8YYYY 
-- 8___  0   0 0    0   0 8   8 8___Y 0    8___  
-- 8"""  0   0 0    0   0 8YYY8 8"""o 0    8"""  
-- 0     "ooo" 8ooo 8oooY 0   0 8ooo" 8ooo 8oooo 

Foldable (Node c h) where
	foldr f z Leaf = z
	foldr f z (NodeB l x r) = foldr f (f x (foldr f z r)) l
	foldr f z (NodeR l x r) = foldr f (f x (foldr f z r)) l

export
Foldable RedBlackTree where
	foldr f z (Tree t) = foldr f z t

-- YY8YY 8YYYo  o8o  0   0 8YYYY 8YYYo oYYYo  o8o  8888. 0    8YYYY
--   0   8___P 8   8 0   0 8___  8___P %___  8   8 8___Y 0    8___ 
--   0   8""Yo 8YYY8 "o o" 8"""  8""Yo `"""p 8YYY8 8"""o 0    8""" 
--   0   0   0 0   0  "8"  8oooo 0   0 YoooY 0   0 8ooo" 8ooo 8oooo

Traversable (Node c h) where
	traverse f Leaf = pure Leaf
	traverse f (NodeB l k r) = [| NodeB (traverse f l) (f k) (traverse f r) |]
	traverse f (NodeR l k r) = [| NodeR (traverse f l) (f k) (traverse f r) |]