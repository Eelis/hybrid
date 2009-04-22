module Types where
import Prelude hiding (Either(..))
data Location =
  Up | Right | Down | Left | -- rotator locations
  Heat | Cool | Check -- thermostat locations
  deriving Eq
data Range =
  I01 | I12 | I23 | I34 | I45 |
  OI_1 | OI12 | OI23 | OI34 | OI4_ |
  CI0_12 | CI_12 | CI12_1 | CI1_2 | CI2_3 | CI3_ | -- thermostat clock intervals
  TIC_3 | TI3_45 | TI45_5 | TI5_6 | TI6_9 | TI9_10 | TI10_ -- thermostat temperature intervals
  deriving (Show, Eq)
data Kind = Cont | Disc deriving Eq
data Vertex = Vertex Kind Location Range Range deriving (Show, Eq)

instance Show Kind where show Cont = "C"; show Disc = "D"
instance Show Location where
  show Left = "L"; show Right = "R"; show Up = "U"; show Down = "D"
  show Heat = "Heat"; show Cool = "Cool"; show Check = "Check"
