module Types where
import Prelude hiding (Either(..))
data Location =
  Up | Right | Down | Left | -- rotator locations
  Heat | Cool | Check -- thermostat locations
  deriving Eq
 
data Kind = Cont | Disc deriving Eq
data Vertex = Vertex Kind Location Integer Integer deriving (Show, Eq)

instance Show Kind where show Cont = "C"; show Disc = "D"
instance Show Location where
  show Left = "L"; show Right = "R"; show Up = "U"; show Down = "D"
  show Heat = "Heat"; show Cool = "Cool"; show Check = "Check"
