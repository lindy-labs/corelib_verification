use debug::PrintTrait;
use core::result;
use core::result::ResultTrait;
use core::integer;
use core::starknet::contract_address::ContractAddress;
use core::starknet;
use core::starknet::SyscallResult;
use core::starknet::SyscallResultTrait;
use core::starknet::info::ExecutionInfo;
use core::array::ArrayTrait;

fn main(contract_address : ContractAddress,
  syscall_result_contract_address : SyscallResult<ContractAddress>,
  syscall_result_u8 : SyscallResult<u8>,
  syscall_result_u128 : SyscallResult<u128>,
  syscall_result_unit : SyscallResult<()>,
  syscall_result_box_execution_info : SyscallResult<Box<ExecutionInfo>>,
  syscall_result_span_felt252 : SyscallResult<Span<felt252>>,
  syscall_result_u256 : SyscallResult<u256>,
  syscall_result_felt252 : SyscallResult<felt252>,
  syscall_result_bool : SyscallResult<bool>) {
    //core::result::ResultTraitImpl<core::integer::u32, core::integer::u32>::expect<core::integer::u32Drop>();
    let x : Result<u32, u32> = Result::Ok(0_u32);
    let x : u32 = x.expect('foo');
    //core::result::ResultTraitImpl<core::integer::u64, core::integer::u64>::expect<core::integer::u64Drop>
    let x : Result<u64, u64> = Result::Ok(0_u64);
    let x : u64 = x.expect('foo');
    //core::result::ResultTraitImpl<core::integer::u8, core::integer::u8>::expect<core::integer::u8Drop>
    let x : Result<u8, u8> = Result::Ok(0_u8);
    let x : u8 = x.expect('foo');
    //core::integer::U8Sub::sub
    let x = 42_u8 - 23_u8;
    //core::integer::u128_checked_mul
    let x = core::integer::u128_checked_mul(0_u128, 0_u128);
    //core::integer::U128Mul::mul
    let x = core::integer::U128Mul::mul(0_u128, 0_u128);
    //core::result::ResultTraitImpl<core::integer::u128, core::integer::u128>::expect<core::integer::u128Drop>
    let x : Result<u128, u128> = Result::Ok(0_u128);
    let x : u128 = x.expect('foo');
    //core::integer::U128Sub::sub
    let x = core::integer::U128Sub::sub(0, 0);
    //core::integer::u128_try_from_felt252
    let x = core::integer::u128_try_from_felt252(0);
    //core::integer::U128BitNot::bitnot
    let x = core::integer::U128BitNot::bitnot(0);
    //core::integer::u64_try_as_non_zero
    let x = core::integer::u64_try_as_non_zero(0);
    //core::integer::u128_try_as_non_zero
    let x = core::integer::u128_try_as_non_zero(0);
    //core::integer::u256_try_as_non_zero
    let x = core::integer::u256_try_as_non_zero(0);
    //core::integer::u64_as_non_zero
    let x = core::integer::u64_as_non_zero(0);
    //core::integer::u128_as_non_zero
    let x = core::integer::u128_as_non_zero(0);
    //core::integer::u256_as_non_zero
    let x = core::integer::u256_as_non_zero(0);
    //core::integer::u256_from_felt252
    let x = core::integer::u256_from_felt252(0);
    //core::integer::U64TryIntoNonZero::try_into
    let x = core::integer::U64TryIntoNonZero::try_into(0);
    //core::integer::U128TryIntoNonZero::try_into
    let x = core::integer::U128TryIntoNonZero::try_into(0);
    //core::integer::U256TryIntoNonZero::try_into
    let x = core::integer::U256TryIntoNonZero::try_into(0);
    //core::integer::Felt252TryIntoU8::try_into
    let x = core::integer::Felt252TryIntoU8::try_into(0);
    //core::integer::Felt252TryIntoU32::try_into
    let x = core::integer::Felt252TryIntoU32::try_into(0);
    //core::integer::Felt252TryIntoU64::try_into
    let x = core::integer::Felt252TryIntoU64::try_into(0);
    //core::integer::U32Add::add
    let x = core::integer::U32Add::add(0, 0);
    //core::integer::U32Sub::sub
    let x = core::integer::U32Sub::sub(0, 0);
    //core::integer::U64Add::add
    let x = core::integer::U64Add::add(0, 0);
    //core::integer::U64Sub::sub
    let x = core::integer::U64Sub::sub(0, 0);
    //core::integer::U64Div::div
    let x = core::integer::U64Div::div(0, 0);
    //core::integer::U128Div::div
    let x = core::integer::U128Div::div(0, 0);
    //core::integer::U128Add::add
    let x = core::integer::U128Add::add(0, 0);
    //core::integer::u256_overflowing_add
    let x = core::integer::u256_overflowing_add(0, 0);
    //core::integer::u256_checked_add
    let x = core::integer::u256_checked_add(0, 0);
    //core::integer::U256Add::add
    let x = core::integer::U256Add::add(0, 0);
    //core::integer::u256_overflow_sub
    let x = core::integer::u256_overflow_sub(0, 0);
    //core::integer::u256_checked_sub
    let x = core::integer::u256_checked_sub(0, 0);
    //core::integer::U256Sub::sub
    let x = core::integer::U256Sub::sub(0, 0);
    //core::integer::u256_overflow_mul
    let x = core::integer::u256_overflow_mul(0, 0);
    //core::integer::u256_checked_mul
    let x = core::integer::u256_checked_mul(0, 0);
    //core::integer::U256Mul::mul
    let x = core::integer::U256Mul::mul(0, 0);
    //core::integer::U256PartialOrd::lt
    let x = core::integer::U256PartialOrd::lt(0, 0);
    //core::integer::U256Div::div
    let x = core::integer::U256Div::div(0, 0);
    //core::hash::LegacyHashContractAddress::hash
    let x = core::hash::LegacyHashContractAddress::hash(0, contract_address);
    //core::starknet::contract_address::Felt252TryIntoContractAddress::try_into
    let x = core::starknet::contract_address::Felt252TryIntoContractAddress::try_into(0);
    //core::starknet::info::get_execution_info
    let x = core::starknet::info::get_execution_info();
    //core::starknet::info::get_caller_address
    let x = core::starknet::info::get_caller_address();
    //core::starknet::info::get_block_info
    let x = core::starknet::info::get_block_info();
    //core::starknet::info::get_contract_address
    let x = core::starknet::info::get_contract_address();
    //core::starknet::info::get_block_timestamp
    let x = core::starknet::info::get_block_timestamp();
    //core::starknet::SyscallResultTraitImpl<core::starknet::contract_address::ContractAddress>::unwrap_syscall
    let x = syscall_result_contract_address.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::integer::u8>::unwrap_syscall
    let x = syscall_result_u8.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::integer::u128>::unwrap_syscall
    let x = syscall_result_u128.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<()>::unwrap_syscall
    let x = syscall_result_unit.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::box::Box<core::starknet::info::ExecutionInfo>>::unwrap_syscall
    let x = syscall_result_box_execution_info.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::array::Span<core::felt252>>::unwrap_syscall
    let x = syscall_result_span_felt252.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::integer::u256>::unwrap_syscall
    let x = syscall_result_u256.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::felt252>::unwrap_syscall
    let x = syscall_result_felt252.unwrap_syscall();
    //core::starknet::SyscallResultTraitImpl<core::bool>::unwrap_syscall
    let x = syscall_result_bool.unwrap_syscall();
}