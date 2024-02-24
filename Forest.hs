
module Forest where
    
    data BinaryPathTree a = EmptyPathTerm | PathTerm a 
                            | PathLeft a (BinaryPathTree a) (BinaryTree a)
                            | PathRight a (BinaryTree a) (BinaryPathTree a) deriving Show

    data BinaryTree a = EmptyLeaf | Leaf a 
                        | Inner a (BinaryTree a) (BinaryTree a) 
                        | InnerLeft a (BinaryPathTree a) (BinaryTree a)
                        | InnerRight a (BinaryTree a) (BinaryPathTree a) deriving Show                    
    
    newtype DfsInfixBinaryTree a = DfsInfix (BinaryTree a)
    newtype DfsPrefixBinaryTree a = DfsPrefix (BinaryTree a)
    newtype DfsPostfixBinaryTree a = DfsPostfix (BinaryTree a)

    normalize (PathLeft a l r) = Inner a (normalize l) r
    normalize (PathRight a l r) = Inner a l (normalize r)
    normalize (PathTerm a) = Leaf a
    normalize EmptyPathTerm = EmptyLeaf  


    -- Foldable Instances appear to be all generated results in reverse order of what they should be.

    instance Foldable DfsInfixBinaryTree where
        foldr f accum (DfsInfix tree) = descend accum tree
            where descend acc (Inner a l r) = descend (f a (descend acc r)) l
                  descend acc (InnerLeft a l r) = descendP (f a (descend acc r)) l
                  descend acc (InnerRight a l r) = descend (f a (descendP acc r)) l
                  descend acc (Leaf a) = f a acc
                  descend acc EmptyLeaf = acc
                  descendP acc (PathLeft a l r) = descendP (f a (descend acc r)) l
                  descendP acc (PathRight a l r) = descend (f a (descendP acc r)) l
                  descendP acc (PathTerm a) = f a acc
                  descendP acc EmptyPathTerm = acc

    instance Foldable DfsPrefixBinaryTree where
        foldr f accum (DfsPrefix tree) = descend accum tree
            where descend acc (Inner a l r) = f a (descend (descend acc r) l)
                  descend acc (InnerLeft a l r) = f a (descendP (descend acc r) l)
                  descend acc (InnerRight a l r) = f a (descend (descendP acc r) l)
                  descend acc (Leaf a) = f a acc
                  descend acc EmptyLeaf = acc
                  descendP acc (PathLeft a l r) = f a (descendP (descend acc r) l)
                  descendP acc (PathRight a l r) = f a (descend (descendP acc r) l)
                  descendP acc (PathTerm a) = f a acc
                  descendP acc EmptyPathTerm = acc
    
    instance Foldable DfsPostfixBinaryTree where
        foldr f accum (DfsPostfix tree) = descend accum tree
            where descend acc (Inner a l r) = descend (descend (f a acc) l) r
                  descend acc (InnerLeft a l r) = descend (descendP (f a acc) l) r
                  descend acc (InnerRight a l r) = descendP (descend (f a acc) l) r
                  descend acc (Leaf a) = f a acc
                  descend acc EmptyLeaf = acc
                  descendP acc (PathLeft a l r) = descend (descendP (f a acc) l) r
                  descendP acc (PathRight a l r) = descendP (descend (f a acc) l) r
                  descendP acc (PathTerm a) = f a acc
                  descendP acc EmptyPathTerm = acc

    instance Foldable BinaryPathTree where
        foldr f = descend
            where descend acc (PathLeft a l _) = f a (descend acc l)
                  descend acc (PathRight a _ r) = f a (descend acc r)
                  descend acc (PathTerm a) = f a acc
                  descend acc EmptyPathTerm = acc              

    instance Functor BinaryTree where
        fmap f = descend
             where descend EmptyLeaf = EmptyLeaf
                   descend (Leaf a) = Leaf (f a)
                   descend (Inner a l r) = Inner (f a) (descend l) (descend r)
                   descend (InnerLeft a path tree) = InnerLeft (f a) (fmap f path) (descend tree)
                   descend (InnerRight a tree path) = InnerRight (f a) (descend tree) (fmap f path)

    instance Functor BinaryPathTree where
        fmap f = descend
             where descend EmptyPathTerm = EmptyPathTerm
                   descend (PathTerm a) = PathTerm (f a)
                   descend (PathLeft a path tree) = PathLeft (f a) (descend path) (fmap f tree)
                   descend (PathRight a tree path) = PathRight (f a) (fmap f tree) (descend path)                                
     
    instance (Eq a) => Eq (BinaryTree a) where
        EmptyLeaf == EmptyLeaf = True
        Leaf l == Leaf r = l == r
        Inner m ls lt == Inner n rs rt = (m == n) && (ls == rs && lt == rt)
        InnerLeft m lpath ltree == InnerLeft n rpath rtree = (m == n) && (lpath == rpath) && (ltree == rtree)
        InnerRight m ltree lpath == InnerRight n rtree rpath = (m == n) && (lpath == rpath) && (ltree == rtree) 
        _ == _ = False

    instance (Eq a) => Eq (BinaryPathTree a) where
        EmptyPathTerm == EmptyPathTerm = True
        PathTerm m == PathTerm n = m == n
        PathLeft m lpath ltree == PathLeft n rpath rtree = (m == n) && (lpath == rpath) && (ltree == rtree)
        PathRight m ltree lpath == PathRight n rtree rpath = (m == n) && (lpath == rpath) && (ltree == rtree)
        _ == _ = False

    instance Semigroup (BinaryPathTree a) where
        l <> r = descend l r
            where descend (PathLeft a (PathTerm b) t) rpath = PathLeft a (PathLeft b rpath EmptyLeaf) t
                  descend (PathLeft a EmptyPathTerm t) rpath = PathLeft a rpath t
                  descend (PathLeft a cont t) rpath = PathLeft a (descend cont rpath) t
                  descend (PathRight a t (PathTerm b)) rpath = PathRight a t (PathLeft b rpath EmptyLeaf)
                  descend (PathRight a t EmptyPathTerm) rpath = PathRight a t rpath 
                  descend (PathRight a t cont) rpath = PathRight a t (descend cont rpath)         
                  descend (PathTerm a) _ = PathLeft a (PathTerm a) EmptyLeaf
                  descend EmptyPathTerm rpath = rpath

    instance Monoid (BinaryPathTree a) where
        mempty = EmptyPathTerm

    -- traverse the path to the terminal
    seek :: BinaryPathTree a -> BinaryPathTree a
    seek (PathLeft _ l _) = seek l
    seek (PathRight _ _ r) = seek r
    seek (PathTerm t) = PathTerm t
    seek EmptyPathTerm = EmptyPathTerm

    -- unit BPT construction
    unitLeft = PathLeft () EmptyPathTerm EmptyLeaf
    unitRight = PathRight () EmptyLeaf EmptyPathTerm
    unitTerm = PathTerm ()

    -- BPT construction combinator
    pcoc :: BinaryPathTree a -> BinaryPathTree a -> BinaryPathTree a
    pcoc (PathLeft a _ r) t = PathLeft a t r
    pcoc (PathRight a l _) t = PathRight a l t
    pcoc _ t = t      -- Terminals are replaced during folding

    select :: BinaryPathTree () -> BinaryTree a -> Maybe (BinaryPathTree a)
    select (PathLeft _ pl _) (InnerLeft a tl tr) = 
        case select pl (normalize tl) of
            Just c -> Just(PathLeft a c tr)
            Nothing -> Nothing
    select (PathRight _ _ pr) (InnerRight a tl tr) = 
        case select pr (normalize tr) of
            Just c -> Just(PathRight a tl c)
            Nothing -> Nothing
    select (PathTerm _) (Leaf a) = Just (PathTerm a)
    select EmptyPathTerm EmptyLeaf = Just EmptyPathTerm
    select _ _ = Nothing

    -- SampleTrees
    
    sample1 = PathRight 1 (Inner 2 (Leaf 3) (Leaf 4)) (PathLeft 5 (PathTerm 6) (Leaf 7))
    sample2 = fmap (*10) sample1

    sample3 = sample1 <> sample2

    sample4 = foldr (:) [] $ DfsInfix (normalize sample3)
    sample5 = foldr (:) [] sample1

    sample6 = foldr pcoc EmptyPathTerm [unitLeft, unitRight, unitLeft, unitTerm]

    sample7 = foldr pcoc EmptyPathTerm [unitRight, unitLeft, unitTerm]
    sample8 = select sample7 (normalize sample1)