module Types where
import Prelude hiding (Either(..))
data Location = Up | Right | Down | Left deriving Eq
data Range = I01 | I12 | I23 | I34 | I45 | OI_1 | OI12 | OI23 | OI34 | OI4_ deriving (Show, Eq)
data Kind = Cont | Disc deriving Eq
data Vertex = Vertex Kind Location Range Range deriving (Show, Eq)

instance Show Kind where show Cont = "C"; show Disc = "D"
instance Show Location where show Left = "L"; show Right = "R"; show Up = "U"; show Down = "D"
