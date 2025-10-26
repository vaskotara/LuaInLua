local unpack = table and table.unpack or unpack;
local getfenv = getfenv or function()
	return _ENV or _G or nil
end;
local LFIELDS_PER_FLUSH = 50;
local Opcodes = {
	MOVE = 0,
	LOADK = 1,
	LOADBOOL = 2,
	LOADNIL = 3,
	GETUPVAL = 4,
	GETGLOBAL = 5,
	GETTABLE = 6,
	SETGLOBAL = 7,
	SETUPVAL = 8,
	SETTABLE = 9,
	NEWTABLE = 10,
	SELF = 11,
	ADD = 12,
	SUB = 13,
	MUL = 14,
	DIV = 15,
	MOD = 16,
	POW = 17,
	UNM = 18,
	NOT = 19,
	LEN = 20,
	CONCAT = 21,
	JMP = 22,
	EQ = 23,
	LT = 24,
	LE = 25,
	TEST = 26,
	TESTSET = 27,
	CALL = 28,
	TAILCALL = 29,
	RETURN = 30,
	FORLOOP = 31,
	FORPREP = 32,
	TFORLOOP = 33,
	SETLIST = 34,
	CLOSE = 35,
	CLOSURE = 36,
	VARARG = 37
}
local function getOp(i)
	return i % 64
end;
local function getA(i)
	return math.floor(i / 64) % 256
end;
local function getC(i)
	return math.floor(i / 16384) % 512
end;
local function getB(i)
	return math.floor(i / 8388608) % 512
end;
local function getBx(i)
	return math.floor(i / 16384)
end;
local function getSBx(i)
	return getBx(i) - 131071
end;
local function isK(rk)
	return rk > 255
end;
local function getRk(constants, stack_base, stack, rk_val)
	if isK(rk_val) then
		return constants[rk_val - 255]
	else
		return stack[stack_base + rk_val]
	end
end;
local Closure = {
	__index = {
		is_closure = true
	}
}
local Upvalue = {
	__index = {
		is_upvalue = true
	}
}
local Parser = {}
function Parser.parse(bytecode)
	local pos = 1;
	local isLittleEndian = true;
	local function read(n)
		if pos + n - 1 > #bytecode then
			error("Unexpected end of bytecode chunk")
		end;
		local result = bytecode:sub(pos, pos + n - 1)
		pos = pos + n;
		return result
	end;
	local function readByte()
		return string.byte(read(1))
	end;
	local function readInt()
		local b1, b2, b3, b4 = string.byte(read(4), 1, 4)
		return isLittleEndian and (b1 + b2 * 256 + b3 * 65536 + b4 * 16777216) or (b4 + b3 * 256 + b2 * 65536 + b1 * 16777216)
	end;
	local function readSizeT()
		return readInt()
	end;
	local function readString(size)
		return read(size):gsub("\0$", "")
	end;
	local function readNumber()
		local bytes = {
			string.byte(read(8), 1, 8)
		}
		if not isLittleEndian then
			table.reverse(bytes)
		end;
		local b1, b2, b3, b4, b5, b6, b7, b8 = unpack(bytes)
		local sign = (b8 >= 128) and -1 or 1;
		local exponent = (b8 % 128) * 16 + math.floor(b7 / 16)
		local mantissa = (b7 % 16) * (2 ^ 48) + b6 * (2 ^ 40) + b5 * (2 ^ 32) + b4 * (2 ^ 24) + b3 * (65536) + b2 * (256) + b1;
		if exponent == 2047 then
			return (mantissa == 0) and (sign * 1 / 0) or (0 / 0)
		end;
		return sign * ((exponent == 0) and (mantissa * 3.4175792574734563e-227) or ((1 + mantissa / 2 ^ 52) * 2 ^ (exponent - 1023)))
	end;
	if read(4) ~= "\27Lua" then
		error("Invalid Lua 5.1 bytecode magic number")
	end;
	if readByte() ~= 81 then
		error("Unsupported Lua version")
	end;
	read(1)
	isLittleEndian = (readByte() == 1)
	read(5)
	local function parseFunction()
		local p = {
			sourceName = readString(readSizeT()),
			lineDefined = readInt(),
			lastLineDefined = readInt(),
			numUpvalues = readByte(),
			numParams = readByte(),
			isVararg = readByte(),
			maxStackSize = readByte(),
			instructions = {},
			constants = {},
			prototypes = {}
		}
		local numInstructions = readInt()
		for _ = 1, numInstructions do
			table.insert(p.instructions, readInt())
		end;
		local numConstants = readInt()
		for _ = 1, numConstants do
			local t = readByte()
			if t == 0 then
				table.insert(p.constants, nil)
			elseif t == 1 then
				table.insert(p.constants, readByte() ~= 0)
			elseif t == 3 then
				table.insert(p.constants, readNumber())
			elseif t == 4 then
				table.insert(p.constants, readString(readSizeT()))
			end
		end;
		local numPrototypes = readInt()
		for _ = 1, numPrototypes do
			table.insert(p.prototypes, parseFunction())
		end;
		pos = pos + readInt() * 4;
		for _ = 1, readInt() do
			readString(readSizeT())
			readInt()
			readInt()
		end;
		for _ = 1, readInt() do
			readString(readSizeT())
		end;
		return p
	end;
	return parseFunction()
end;
local VM = {}
local function execute(main_proto, vm_env, ...)
	local stack = {}
	local call_stack = {}
	local open_upvalues = {}
	local main_closure = setmetatable({
		proto = main_proto,
		upvalues = {},
		env = vm_env
	}, Closure)
	local ci = {
		closure = main_closure,
		pc = 1,
		base = 1,
		varargs = {
			...
		},
		n_results = -1
	}
	table.insert(call_stack, ci)
	stack[ci.base] = main_closure;
	for i = 1, main_proto.numParams do
		stack[ci.base + i] = ci.varargs[i]
	end;
	while true do
		local i = ci.closure.proto.instructions[ci.pc]
		ci.pc = ci.pc + 1;
		local op, a, b, c = getOp(i), getA(i), getB(i), getC(i)
		local bx, sbx = getBx(i), getSBx(i)
		local ra = a + ci.base;
		local proto_consts = ci.closure.proto.constants;
		if op == Opcodes.MOVE then
			stack[ra] = stack[b + ci.base]
		elseif op == Opcodes.LOADK then
			stack[ra] = proto_consts[bx + 1]
		elseif op == Opcodes.LOADBOOL then
			stack[ra] = (b ~= 0)
			if c ~= 0 then
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.LOADNIL then
			for j = ra, b + ci.base do
				stack[j] = nil
			end
		elseif op == Opcodes.GETUPVAL then
			stack[ra] = ci.closure.upvalues[b + 1].value
		elseif op == Opcodes.SETUPVAL then
			ci.closure.upvalues[b + 1].value = stack[ra]
		elseif op == Opcodes.GETGLOBAL then
			stack[ra] = ci.closure.env[proto_consts[bx + 1]]
		elseif op == Opcodes.SETGLOBAL then
			ci.closure.env[proto_consts[bx + 1]] = stack[ra]
		elseif op == Opcodes.NEWTABLE then
			stack[ra] = {}
		elseif op == Opcodes.GETTABLE then
			local rb = b + ci.base;
			stack[ra] = stack[rb][getRk(proto_consts, ci.base, stack, c)]
		elseif op == Opcodes.SETTABLE then
			stack[ra][getRk(proto_consts, ci.base, stack, b)] = getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.SELF then
			local rb = b + ci.base;
			stack[ra + 1] = stack[rb]
			stack[ra] = stack[rb][getRk(proto_consts, ci.base, stack, c)]
		elseif op == Opcodes.ADD then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) + getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.SUB then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) - getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.MUL then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) * getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.DIV then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) / getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.MOD then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) % getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.POW then
			stack[ra] = getRk(proto_consts, ci.base, stack, b) ^ getRk(proto_consts, ci.base, stack, c)
		elseif op == Opcodes.UNM then
			stack[ra] = -stack[b + ci.base]
		elseif op == Opcodes.NOT then
			stack[ra] = not stack[b + ci.base]
		elseif op == Opcodes.LEN then
			stack[ra] = #stack[b + ci.base]
		elseif op == Opcodes.CONCAT then
			local s = stack[c + ci.base]
			for j = c + ci.base - 1, b + ci.base, -1 do
				s = stack[j] .. s
			end;
			stack[ra] = s
		elseif op == Opcodes.JMP then
			ci.pc = ci.pc + sbx
		elseif op == Opcodes.EQ then
			if (getRk(proto_consts, ci.base, stack, b) == getRk(proto_consts, ci.base, stack, c)) ~= (a ~= 0) then
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.LT then
			if (getRk(proto_consts, ci.base, stack, b) < getRk(proto_consts, ci.base, stack, c)) ~= (a ~= 0) then
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.LE then
			if (getRk(proto_consts, ci.base, stack, b) <= getRk(proto_consts, ci.base, stack, c)) ~= (a ~= 0) then
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.TEST then
			if not stack[ra] == (c ~= 0) then
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.TESTSET then
			local rb = b + ci.base;
			if not stack[rb] == (c ~= 0) then
				ci.pc = ci.pc + 1
			else
				stack[ra] = stack[rb]
			end
		elseif op == Opcodes.FORPREP then
			stack[ra] = stack[ra] - stack[ra + 2]
			ci.pc = ci.pc + sbx
		elseif op == Opcodes.FORLOOP then
			local idx, limit, step = stack[ra], stack[ra + 1], stack[ra + 2]
			idx = idx + step;
			stack[ra] = idx;
			if (step > 0 and idx <= limit) or (step < 0 and idx >= limit) then
				ci.pc = ci.pc + sbx;
				stack[ra + 3] = idx
			end
		elseif op == Opcodes.TFORLOOP then
			local results = {
				pcall(stack[ra], stack[ra + 1], stack[ra + 2])
			}
			if not results[1] then
				error(results[2])
			end;
			table.remove(results, 1)
			if results[1] ~= nil then
				stack[ra + 2] = results[1]
				for j = 1, c do
					stack[ra + 2 + j] = results[j]
				end
			else
				ci.pc = ci.pc + 1
			end
		elseif op == Opcodes.SETLIST then
			local n = b;
			if n == 0 then
				n = #stack - ra
			end;
			local c_val = c;
			if c_val == 0 then
				c_val = getBx(ci.closure.proto.instructions[ci.pc])
				ci.pc = ci.pc + 1
			end;
			local offset = (c_val - 1) * LFIELDS_PER_FLUSH;
			for j = 1, n do
				stack[ra][offset + j] = stack[ra + j]
			end
		elseif op == Opcodes.CLOSE then
			for j = #open_upvalues, 1, -1 do
				local uv = open_upvalues[j]
				if uv.stack_idx >= ra then
					uv.value = stack[uv.stack_idx]
					uv.is_open = false;
					table.remove(open_upvalues, j)
				else
					break
				end
			end
		elseif op == Opcodes.CLOSURE then
			local p = ci.closure.proto.prototypes[bx + 1]
			local cl = setmetatable({
				proto = p,
				upvalues = {},
				env = ci.closure.env
			}, Closure)
			for j = 1, p.numUpvalues do
				local up_i = ci.closure.proto.instructions[ci.pc]
				ci.pc = ci.pc + 1;
				local up_op, up_b = getOp(up_i), getA(up_i)
				if up_op == Opcodes.MOVE then
					local stack_idx = up_b + ci.base;
					local found_uv;
					for _, uv in ipairs(open_upvalues) do
						if uv.stack_idx == stack_idx then
							found_uv = uv;
							break
						end
					end;
					if found_uv then
						cl.upvalues[j] = found_uv
					else
						local new_uv = setmetatable({
							value = stack[stack_idx],
							stack_idx = stack_idx,
							is_open = true
						}, Upvalue)
						cl.upvalues[j] = new_uv;
						table.insert(open_upvalues, new_uv)
					end
				elseif up_op == Opcodes.GETUPVAL then
					cl.upvalues[j] = ci.closure.upvalues[up_b + 1]
				end
			end;
			stack[ra] = cl
		elseif op == Opcodes.VARARG then
			local n = b - 1;
			if n == -1 then
				n = #ci.varargs
			end;
			for j = 1, n do
				stack[ra + j - 1] = ci.varargs[j]
			end
		elseif op == Opcodes.CALL or op == Opcodes.TAILCALL then
			local n_args = b - 1;
			local n_ret = c - 1;
			local func = stack[ra]
			if not func then
				error("attempt to call a nil value at " .. ci.closure.proto.sourceName .. ":" .. ci.pc)
			end;
			if func.is_closure then
				if op == Opcodes.TAILCALL then
					for j = 0, n_args do
						stack[ci.base - 1 + j] = stack[ra + j]
					end;
					ci.closure, ci.pc, ci.varargs = func, 1, {
						unpack(stack, ra + 1, ra + n_args)
					}
				else
					local new_ci = {
						closure = func,
						pc = 1,
						base = ra,
						varargs = {
							unpack(stack, ra + 1, ra + n_args)
						},
						n_results = n_ret,
						caller = ci
					}
					table.insert(call_stack, new_ci)
					ci = new_ci
				end
			else
				local args = {}
				for j = 1, n_args do
					args[j] = stack[ra + j]
				end;
				local results = {
					pcall(func, unpack(args))
				}
				if not results[1] then
					error(results[2])
				end;
				table.remove(results, 1)
				local ret_base = ra;
				if n_ret ~= -1 then
					for j = 1, n_ret do
						stack[ret_base + j - 1] = results[j]
					end
				else
					for j = 1, #results do
						stack[ret_base + j - 1] = results[j]
					end
				end
			end
		elseif op == Opcodes.RETURN then
			local n_ret = b - 1;
			local returns = {}
			if n_ret == -1 then
				for j = ra, #stack do
					table.insert(returns, stack[j])
				end
			else
				for j = 0, n_ret - 1 do
					table.insert(returns, stack[ra + j])
				end
			end;
			for j = #open_upvalues, 1, -1 do
				if open_upvalues[j].stack_idx >= ci.base then
					table.remove(open_upvalues, j)
				end
			end;
			table.remove(call_stack)
			local caller = ci.caller;
			if not caller then
				return unpack(returns)
			end;
			local ret_base = ci.base
			if caller.n_results ~= -1 then
				for j = 1, caller.n_results do
					stack[ret_base + j - 1] = returns[j]
				end
			else
				for j = 1, #returns do
					stack[ret_base + j - 1] = returns[j]
				end
			end
			ci = caller
		else
			error("Unsupported opcode: " .. op)
		end
	end
end;
function VM.load(bytecode, env)
	local main_proto = Parser.parse(bytecode)
	local vm_env = env or getfenv(2)
	if not vm_env then
		error("An environment table must be provided in this Lua environment.")
	end;
	return function(...)
		return execute(main_proto, vm_env, ...)
	end
end;
return VM
