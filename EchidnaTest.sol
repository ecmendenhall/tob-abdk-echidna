// SPDX-License-Identifier: BSD-4-Clause
pragma solidity ^0.8.1;

import "ABDKMath64x64.sol";

contract Test {
   int128 internal zero = ABDKMath64x64.fromInt(0);
   int128 internal one = ABDKMath64x64.fromInt(1);
   int128 internal negOne = ABDKMath64x64.fromInt(-1);

   int256 internal constant FROM_INT_MIN_VALUE = -0x8000000000000000;
   int256 internal constant FROM_INT_MAX_VALUE = 0x7FFFFFFFFFFFFFFF;

   uint256 internal constant FROM_UINT_MAX_VALUE = 0x7FFFFFFFFFFFFFFF;

   int128 internal constant MIN_64x64 = -0x80000000000000000000000000000000;
   int128 internal constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

   event Value(string, int64);
   event Value256(string, int256);

   function debug(string memory x, int128 y) internal {
     emit Value(x, ABDKMath64x64.toInt(y));
   }

   function debug256(string memory x, int256 y) internal {
     emit Value256(x, y);
   }

   function add(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.add(x, y);
   }

   function sub(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.sub(x, y);
   }

   function mul(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.mul(x, y);
   }

   function muli(int128 x, int256 y) internal pure returns (int256) {
     return ABDKMath64x64.muli(x, y);
   }

   function mulu(int128 x, uint256 y) internal pure returns (uint256) {
     return ABDKMath64x64.mulu(x, y);
   }

   function div(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.div(x, y);
   }

   function divi(int256 x, int256 y) internal pure returns (int128) {
     return ABDKMath64x64.divi(x, y);
   }

   function divu(uint256 x, uint256 y) internal pure returns (int128) {
     return ABDKMath64x64.divu(x, y);
   }

   function fromInt(int256 x) public pure returns (int128) {
     return ABDKMath64x64.fromInt(x);
   }

   function toInt(int128 x) public pure returns (int128) {
     return ABDKMath64x64.toInt(x);
   }

   function fromUInt(uint256 x) public pure returns (int128) {
     return ABDKMath64x64.fromUInt(x);
   }

   function toUInt(int128 x) public pure returns (uint64) {
     return ABDKMath64x64.toUInt(x);
   }

   function from128x128(int256 x) public pure returns (int128) {
     return ABDKMath64x64.from128x128(x);
   }

   function to128x128(int128 x) public pure returns (int256) {
     return ABDKMath64x64.to128x128(x);
   }

   function pow(int128 x, uint256 y) internal pure returns (int128) {
     return ABDKMath64x64.pow(x, y);
   }

   function neg(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.neg(x);
   }

   function inv(int128 x) public pure returns (int128) {
     return ABDKMath64x64.inv(x);
   }

   function sqrt(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.sqrt(x);
   }

   function abs(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.abs(x);
   }

   function log_2(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.log_2(x);
   }

   function exp_2(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.exp_2(x);
   }

   function ln(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.ln(x);
   }

   function exp(int128 x) internal pure returns (int128) {
     return ABDKMath64x64.exp(x);
   }

   function avg(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.avg(x, y);
   }

   function gavg(int128 x, int128 y) internal pure returns (int128) {
     return ABDKMath64x64.gavg(x, y);
   }

   /// @dev Minimum value for fromInt
   function test_fromInt_min_value(int256 x) public view {
     if(x >= FROM_INT_MIN_VALUE) return; // Reject inputs >= min value

     // Function should always revert
     try this.fromInt(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev Maximum value for fromInt
   function test_fromInt_max_value(int256 x) public view {
     if(x <= FROM_INT_MAX_VALUE) return; // Reject inputs <= max value

     // Function should always revert
     try this.fromInt(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev In-range values for fromInt
   function test_fromInt_in_range(int256 x) public view {
     if(x < FROM_INT_MIN_VALUE) return; // Reject inputs < min value
     if(x > FROM_INT_MAX_VALUE) return; // Reject inputs > max value

     // Function should never revert
     try this.fromInt(x) { } catch Error(string memory) { assert(false); }
   }

   /// @dev Any valid value created with `fromInt` converts using `toInt`
   function test_valid_fromInt_converts_toInt(int256 x) public view {
     if(x < FROM_INT_MIN_VALUE) return; // Reject inputs < min value
     if(x > FROM_INT_MAX_VALUE) return; // Reject inputs > max value

     // Function should never revert
     try this.toInt(fromInt(x)) { } catch Error(string memory) {
       assert(false);
     }
   }

   /// @dev Maximum value for fromUInt
   function test_fromUInt_max_value(uint256 x) public view {
     if(x <= FROM_UINT_MAX_VALUE) return; // Reject inputs <= max value

     // Function should always revert
     try this.fromUInt(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev In-range values for fromInt
   function test_fromUInt_in_range(uint256 x) public view {
     if(x > FROM_UINT_MAX_VALUE) return; // Reject inputs > max value

     // Function should never revert
     try this.fromUInt(x) { } catch Error(string memory) {
       assert(false);
     }
   }

   /// @dev Any valid value created with `fromUInt` converts using `toUInt`
   function test_valid_fromUInt_converts_toUInt(uint256 x) public view {
     if(x > FROM_UINT_MAX_VALUE) return; // Reject inputs > max value

     // Function should never revert
     try this.toUInt(fromUInt(x)) { } catch Error(string memory) {
       assert(false);
     }
   }

   /// @dev `toUint` reverts for negative values
   function test_toUInt_negative_value_reverts(int128 x) public view {
     if(x >= 0) return; // Reject inputs <= max value

     // Function should always revert
     try this.toUInt(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev Minimum value for `from128x128`
   function test_from128x128_min_value(int256 x) public view {
     if(x >> 64 >= MIN_64x64) return; // Reject inputs >= min value

     // Function should always revert
     try this.from128x128(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev Maximum value for from128x128
   function test_from128x128_max_value(int256 x) public view {
     if(x >> 64 <= MAX_64x64) return; // Reject inputs <= max value

     // Function should always revert
     try this.fromInt(x) { assert(false); } catch Error(string memory) {}
   }

   /// @dev In-range values for fromInt
   function test_from128x128_in_range(int256 x) public view {
     if(x >> 64 < MIN_64x64) return; // Reject inputs < min value
     if(x >> 64 > MAX_64x64) return; // Reject inputs > max value

     // Function should never revert
     try this.fromInt(x) { } catch Error(string memory) { assert(false); }
   }

   /// @dev Any valid value created with `from128x128` converts using `to128x128`
   function test_valid_from128x128_converts_to128x128(int256 x) public view {
     if(x >> 64 < MIN_64x64) return; // Reject inputs < min value
     if(x >> 64 > MAX_64x64) return; // Reject inputs > max value

     // Function should never revert
     try this.to128x128(from128x128(x)) { } catch Error(string memory) {
       assert(false);
     }
   }

   /// @dev Commutative property of addition: x + y = y + x
   function test_add_commutative(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(add(x, y) == add(y, x));
   }

   /// @dev Associative property of addition: (x + y) + z = x + (y + z)
   function test_add_associative(int128 x, int128 y, int128 z) public pure {
     x = fromInt(x);
     y = fromInt(y);
     z = fromInt(z);

     assert(add(add(x, y), z) == add(x, add(y, z)));
   }

   /// @dev Identity property of addition: 0 + x = x
   function test_add_identity(int128 x) public pure {
     x = fromInt(x);

     assert(add(0, x) == x);
   }

   /// @dev Anti-commutative property of subtraction: x - y = - (y - x)
   function test_sub_anti_commutative(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(sub(x, y) == neg(sub(y, x)));
   }

   /// @dev Commutative property of multiplication: x * y = y * x
   function test_mul_commutative(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(mul(x, y) == mul(y, x));
   }

   /// @dev Commutative property of multiplication: x * y = y * x
   function test_muli_commutative(int128 x, int256 y) public {
     int256 x_256 = int256(x);
     x = fromInt(x);
     int128 y_128 = fromInt(y);

     assert(muli(x, y) == muli(y_128, x_256));
   }

   /// @dev Commutative property of multiplication: x * y = y * x
   function test_mulu_commutative(int128 x, uint256 y) public pure {
     uint256 x_u256 = uint256(int256(x));
     x = fromInt(x);
     int128 y_128 = fromInt(int256(y));

     assert(mulu(x, y) == mulu(y_128, x_u256));
   }

   /// @dev Associative property of multiplication: (x * y) * z = x * (y * z)
   function test_mul_associative(int128 x, int128 y, int128 z) public pure {
     x = fromInt(x);
     y = fromInt(y);
     z = fromInt(z);

     assert(mul(mul(x, y), z) == mul(x, mul(y, z)));
   }

   /// @dev Associative property of multiplication: (x * y) * z = x * (y * z)
   function test_muli_associative(int128 x, int256 y, int256 z) public pure {
     x = fromInt(x);
     int128 y_128 = fromInt(y);

     assert(muli(fromInt(muli(x, y)), z) == muli(x, muli(y_128, z)));
   }

   /// @dev Associative property of multiplication: (x * y) * z = x * (y * z)
   function test_mulu_associative(int128 x, uint256 y, uint256 z) public pure {
     x = fromInt(x);
     int128 y_128 = fromInt(int256(y));

     assert(mulu(fromUInt(mulu(x, y)), z) == mulu(x, mulu(y_128, z)));
   }

   /// @dev Distributive property of multiplication: x * (y + z) = (x * y) + (x * z)
   function test_mul_distributive(int128 x, int128 y, int128 z) public pure {
     x = fromInt(x);
     y = fromInt(y);
     z = fromInt(z);

     assert(mul(x, add(y, z)) == add(mul(x, y), mul(x, z)));
   }

   /// @dev Distributive property of multiplication: x * (y + z) = (x * y) + (x * z)
   function test_muli_distributive(int128 x, int256 y, int256 z) public pure {
     x = fromInt(x);
     int128 y_128 = fromInt(y);
     int128 z_128 = fromInt(z);

     assert(muli(x, add(y_128, z_128)) == add(fromInt(muli(x, y)), fromInt(muli(x, z))));
   }

   /// @dev Distributive property of multiplication: x * (y + z) = (x * y) + (x * z)
   function test_mulu_distributive(int128 x, uint256 y, uint256 z) public pure {
     x = fromInt(x);
     int128 y_128 = fromInt(int256(y));
     int128 z_128 = fromInt(int256(z));

     assert(mulu(x, toUInt(add(y_128, z_128))) == toUInt(add(fromUInt(mulu(x, y)), fromUInt(mulu(x, z)))));
   }

   /// @dev Identity property of multiplication: 1 * x = x
   function test_mul_identity(int128 x) public view {
     x = fromInt(x);

     assert(mul(one, x) == x);
   }

   /// @dev Identity property of multiplication: 1 * x = x
   function test_muli_identity(int256 x) public view {
     assert(muli(one, x) == x);
   }

   /// @dev Identity property of multiplication: 1 * x = x
   function test_mulu_identity(uint256 x) public view {
     assert(mulu(one, x) == x);
   }

   /// @dev Zero property of multiplication: 0 * x = 0
   function test_mul_zero_property(int128 x) public view {
     x = fromInt(x);

     assert(mul(zero, x) == zero);
   }

   /// @dev Zero property of multiplication: 0 * x = 0
   function test_muli_zero_property(int256 x) public view {
     assert(muli(zero, x) == 0);
   }

   /// @dev Zero property of multiplication: 0 * x = 0
   function test_mulu_zero_property(uint256 x) public view {
     assert(mulu(zero, x) == 0);
   }

   /// @dev Negation property of multiplication: -1 * x = -x
   function test_mul_negation(int128 x) public view {
     x = fromInt(x);

     assert(mul(negOne, x) == neg(x));
   }

   /// @dev Negation property of multiplication: -1 * x = -x
   function test_muli_negation(int256 x) public view {
     assert(muli(negOne, x) == -x);
   }

   /// @dev  x * y = (x + x ... + x) y times
   function test_mul_equivalent_to_repeated_addition(int128 x, uint8 y_8) public pure {
     if (y_8 > 50) return;
     x = fromInt(x);
     int128 y = fromInt(int256(uint256(y_8)));

     int128 sum;
     for (uint8 i; i < y_8; ++i) {
       sum = add(sum, x);
     }

     assert(mul(x, y) == sum);
   }

   /// @dev x * (1 / x) = 1
   function test_mul_inverse(int128 x) public view {
     x = ABDKMath64x64.fromInt(x);

     int128 inverse = inv(x);
     assert(mul(x, inverse) <= one && mul(x, inverse) >= sub(one, div(one, fromInt(3))));
   }

   // @dev (x * y) / y = x
   function test_div_inverse_of_mul(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(div(mul(x, y), y) == x);
   }

   // @dev (x * y) / y = x
   function test_divi_inverse_of_mul(int128 x, int256 y) public pure {
     x = fromInt(x);

     assert(divi(muli(x, y), y) == x);
   }

   // @dev (x * y) / y = x
   function test_divu_inverse_of_mul(uint256 x, uint256 y) public {
     int128 x_128 = fromInt(int256(x));
     int128 y_128 = fromInt(int256(y));

     debug("lhs", divu(toUInt(mul(x_128, y_128)), y));
     debug("rhs", x_128);
     assert(divu(mulu(x_128, y), y) == x_128);
   }

   /// @dev Exponent rule #1: x^(y + z) = (x^y)  * (x^z)
   function test_pow_exp_rule1(int128 x, int128 y, int128 z) public pure {
     x = fromInt(x);
     y = abs(fromInt(y)); // Ensure y is positive
     z = abs(fromInt(z)); // Ensure z is positive

     assert(pow(x, uint256(uint128(add(y, z)))) == mul(pow(x, uint256(uint128(y))), pow(x, uint256(uint128(z)))));
   }

   /// @dev Exponent rule #2: (x^y)^z = x^(y * z)
   function test_pow_exp_rule2(int128 x, int128 y, int128 z) public pure {
     x = fromInt(x);
     y = abs(fromInt(y)); // Ensure y is positive
     z = abs(fromInt(z)); // Enzure z is positive

     assert(pow(pow(x, uint256(uint128(y))), uint256(uint128(z))) == pow(x, uint256(uint128(mul(y, z)))));
   }

   /// @dev Exponent rule #3: (x * y)^z = (x^y) * (x^z)
   function test_pow_exp_rule3(int128 x, int128 y, uint256 z) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(pow(mul(x, y), z) == mul(pow(x, z), pow(y, z)));
   }

   /// @dev sqrt(x^2) = abs(x)
   function test_sqrt_abs(int128 x) public pure {
     x = fromInt(x);

     assert(sqrt(pow(x, 2)) == abs(x));
   }

   /// @dev sqrt(x * y) = sqrt(x) * sqrt(y)
   //function test_sqrt_mul(int128 x, int128 y) public {
   //  x = abs(fromInt(x)); // Ensure x is positive
   //  y = abs(fromInt(y)); // Ensure y is positive

   //  if (sqrt(x) <= one) return;
   //  if (sqrt(y) <= one) return;
   //  debug("sqrt(x)", sqrt(x));
   //  debug("sqrt(y)", sqrt(y));
   //  debug("lhs", sqrt(mul(x, y)));
   //  debug("rhs", mul(sqrt(x), sqrt(y)));
   //  assert(sqrt(mul(x, y)) == mul(sqrt(x), sqrt(y)));
   //}

   /// @dev log2(2^x) = x
   function test_log_2_exp_2_inv(int128 x) public pure {
     x = abs(fromInt(x)); // Ensure x is positive

     assert(log_2(exp_2(x)) == x);
   }

   /// @dev ln(e^x) = x
   function test_ln_exp_inv(int128 x) public {
     x = abs(fromInt(x));

     debug("exp(x)", exp(x));
     debug("ln(exp(x))", ln(exp(x)));
     debug("x", x);

     assert(ln(exp(x)) <= x);
   }

   /// @dev ln(x * y) = ln(x) + ln(y)
   function test_ln_addition(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(ln(mul(x, y)) == add(ln(x), ln(y)));
   }

   /// @dev avg(x, y) = (x + y) / 2
   function test_avg(int128 x, int128 y) public pure {
     int128 two = fromInt(2);
     x = fromInt(x);
     y = fromInt(y);

     assert(avg(x, y) == div(add(x, y), two));
   }

   /// @dev gavg(x, y) = sqrt(x * y)
   function test_gavg(int128 x, int128 y) public pure {
     x = fromInt(x);
     y = fromInt(y);

     assert(gavg(x, y) == sqrt(mul(x, y)));
   }
}
