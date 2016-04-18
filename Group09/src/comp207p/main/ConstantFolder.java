package comp207p.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.*;
import java.lang.String;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;
import org.apache.bcel.generic.*;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.StoreInstruction;


public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;

	JavaClass original = null;
	JavaClass optimized = null;

	ArrayList normalMultivariateOperationsList = new ArrayList(Arrays.asList(
																"iadd", "ladd", "fadd", "dadd", 
																"isub", "lsub", "fsub", "dadd", 
																"imul", "lmul", "fmul", "dmul",
																"idiv", "ldiv", "fdiv", "ddiv",
																"irem", "lrem", "frem", "drem",
																		"lcmp",	"fcmpg","dcmpg",
																				"fcmpl","dcmpl",
																"ishl", "lshl",
																"ishr", "lshr",
																"iushr","lushr"
																));
	
	ArrayList typeCastOperationList = new ArrayList(Arrays.asList(
																"i2d", "i2f", "i2l",
																"d2i", "d2f", "d2l",
																"f2d", "f2i", "f2l",
																"l2i", "l2d", "l2f"
															));
	ArrayList negOperationList = new ArrayList(Arrays.asList("ineg", "lneg", "fneg", "dneg"));

	ArrayList ldcOperationsList = new ArrayList(Arrays.asList("ldc", "ldc2_w"));

	ArrayList multiValueControlFlowList = new ArrayList(Arrays.asList("if_icmpeq", "if_icmpge", "if_icmpgt", "if_icmple", "if_icmplt", "if_icmpne"));

	ArrayList singleValueControlFlowList = new ArrayList(Arrays.asList("ifeq", "ifge", "ifgt", "ifle", "iflt", "ifne"));

	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}
	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Implement your optimization here

		// perform task 1
		simpleFolding(cgen, cpgen);

		// perform task 2 & 3
		variableFolding(cgen, cpgen);

		cgen.setMajor(50);
		this.optimized = cgen.getJavaClass();
	}


	/* perform folding for variables (int, long, float, double) in the constant pool */
	public void simpleFolding(ClassGen cgen, ConstantPoolGen cpgen) {
		Method[] methods = cgen.getMethods();

		// perform folding on each of the methods
		for (Method m : methods) {
			Code code = m.getCode();
			InstructionList insList = new InstructionList(code.getCode());
			insList.setPositions();

			InstructionHandle[] insHandles = insList.getInstructionHandles();

			for (InstructionHandle insHandle : insHandles) {
				String insName = insHandle.getInstruction().getName();

				if (normalMultivariateOperationsList.contains(insName)) {
					if ((ldcOperationsList.contains(insHandle.getPrev().getInstruction().getName())) 
						&& (ldcOperationsList.contains(insHandle.getPrev().getPrev().getInstruction().getName()))) {
						// found the place to optimise
						try {
							simpleOptimize(cpgen, insList, insHandle, insName);
						} catch (Exception e) {
							System.out.println("Optimize failed");
							e.printStackTrace();
						}
						
					}
					
				}
			}

			insList.setPositions(true);
			MethodGen mgen = new MethodGen(m.getAccessFlags(), m.getReturnType(), m.getArgumentTypes(), null, m.getName(), cgen.getClassName(), insList, cpgen);
       		// set max stack/local
       		mgen.setMaxStack();
       		mgen.setMaxLocals();

        	// generate the new method
        	Method newMethod = mgen.getMethod();
        	// replace the method in the original class
        	cgen.replaceMethod(m, newMethod);
		}
		return;
	}

	public void simpleOptimize(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName) throws Exception {
		//find what exactly the instruction is: add? sub? mul? div? rem?
		Instruction firstIns = insHandle.getPrev().getPrev().getInstruction();
		Instruction secondIns = insHandle.getPrev().getInstruction();
		InstructionHandle optimized = null;
		Object num1, num2;

		if (firstIns instanceof LDC) {
			num1 = ((LDC)firstIns).getValue(cpgen);
		} else {
			num1 = ((LDC2_W)firstIns).getValue(cpgen);
		}

		if (secondIns instanceof LDC) {
			num2 = ((LDC)secondIns).getValue(cpgen);
		} else {
			num2 = ((LDC2_W)secondIns).getValue(cpgen);
		}

		optimized = findOptimizedMultivariateInsHandle(cpgen, insList, insHandle, insName, num1, num2);

		// safety check
		if (optimized == null) {
			throw new Exception();
		}

		//delete the old instructions
		try {
				insList.delete(optimized.getPrev().getPrev());
				insList.delete(optimized.getPrev());
				insList.delete(insHandle);
		} catch (TargetLostException e) {
			 	e.printStackTrace();
		}
		return;
	}


	public void variableFolding(ClassGen cgen, ConstantPoolGen cpgen) {
		Method[] methods = cgen.getMethods();

		// for each methods
		for (Method m : methods) {
			Code code = m.getCode();
			InstructionList insList = new InstructionList(code.getCode());
			HashMap<Integer, Object> localVars = new HashMap<Integer, Object>();
			InstructionHandle[] insHandles = insList.getInstructionHandles();
			insList.setPositions();

			//check if contains loop
			int numOfLoops = containsLoop(insList);
			ArrayList<Integer> startPositions = new ArrayList<Integer>();
			ArrayList<Integer> endPositions = new ArrayList<Integer>();

			if (numOfLoops>0) {
				continue;
			}

			InstructionHandle insHandle = insHandles[0];
			boolean finish = false;

			//for each instuctions
			while (!finish) {
				Instruction ins = insHandle.getInstruction();

				//step 1: findCate
				if (ins instanceof StoreInstruction) {
					//step 2: put it into map

					//step 2.1: get index
					int index = ((StoreInstruction)ins).getIndex();

					//step 2.2: getvalue
					Instruction prevIns = insHandle.getPrev().getInstruction();
					Object value = null;
					if (prevIns instanceof LDC) {
							 value = ((LDC)prevIns).getValue(cpgen);
					} else if (prevIns instanceof LDC2_W) {
							 value = ((LDC2_W)prevIns).getValue(cpgen);
					} else if (prevIns instanceof ConstantPushInstruction) {
							 value = ((ConstantPushInstruction)prevIns).getValue();
					} else {
							System.out.println("Error");
							System.out.println(insHandle.getPosition());
							System.out.println(insHandle.getInstruction().getName().toString());
							System.exit(1);
					} 

					//put them into map
					localVars.put(index, value);

					//delete code
					try {
						// delete 2 lines of code
						insHandle = insHandle.getNext();
						insList.delete(insHandle.getPrev().getPrev());
						insList.delete(insHandle.getPrev());
					} catch (TargetLostException e) {
						e.printStackTrace();
					}
				} else if (isNumericOperation(ins)) {
					//do optimize
					InstructionHandle optimized = null;

					if (isUnaryOperation(ins)) {
						Instruction prevIns = insHandle.getPrev().getInstruction();

						// find the prev value
						Object value = findInstructionValue(cpgen, prevIns, localVars);

						// apply optimization
						String insName = ins.getName();
						if (isTypeCastingOperation(ins)) {
							optimized = findOptimizedTypeCastingInsHandle(cpgen, insList, insHandle, insName, value);
						} else {
							optimized = findOptimizedNegativeInsHandle(cpgen, insList, insHandle, insName, value);
						}

						// delete code
						try {
							// delete 2 lines of code
							insHandle = insHandle.getNext();
							insList.delete(optimized.getPrev());
							insList.delete(insHandle.getPrev());
						} catch (TargetLostException e) {
							e.printStackTrace();
						}

					} else if (isMultivariateOperation(ins)) {
						Instruction prevIns1 = insHandle.getPrev().getPrev().getInstruction();
						Instruction prevIns2 = insHandle.getPrev().getInstruction();

						Object value1 = findInstructionValue(cpgen, prevIns1, localVars);
						Object value2 = findInstructionValue(cpgen, prevIns2, localVars);

						String insName = ins.getName();

						optimized = findOptimizedMultivariateInsHandle(cpgen, insList, insHandle, insName, value1, value2);
						
						// delete code
						try {
							// delete 3 lines of code
							insHandle = insHandle.getNext();
							insList.delete(optimized.getPrev().getPrev());
							insList.delete(optimized.getPrev());
							insList.delete(insHandle.getPrev());
						} catch (TargetLostException e) {
							e.printStackTrace();
						}

					} else if (isMultiControlFlowOperation(ins)) {

						Instruction prevIns1 = insHandle.getPrev().getPrev().getInstruction();
						Instruction prevIns2 = insHandle.getPrev().getInstruction();

						Object value1 = findInstructionValue(cpgen, prevIns1, localVars);
						Object value2 = findInstructionValue(cpgen, prevIns2, localVars);

						String insName = ins.getName();
						
						optimized = findOptimizedMultiControlFlowHandle(cpgen, insList, insHandle, insName, value1, value2);

						insHandle = optimized;
						//delete code process have been done by the function, lots of code have been delete, need to regenerate insList
					} else  {
						// must be single control flow instruction

						Instruction prevIns = insHandle.getPrev().getInstruction();

						// find the prev value
						Object value = findInstructionValue(cpgen, prevIns, localVars);

						String insName = ins.getName();

						optimized = findOptimizedSingleControlFlowHandle(cpgen, insList, insHandle, insName, value);

						insHandle = optimized;

					} 

				} else {
					insHandle = insHandle.getNext();
					//do nothing
				}
				//check finish 
				if (insHandle == insList.getEnd()){
					finish = true;
				}

			}
			insList.setPositions(true);
			MethodGen mgen = new MethodGen(m.getAccessFlags(), m.getReturnType(), m.getArgumentTypes(), null, m.getName(), cgen.getClassName(), insList, cpgen);
       		// set max stack/local
       		mgen.setMaxStack();
       		mgen.setMaxLocals();

        	// generate the new method
        	Method newMethod = mgen.getMethod();
        	// replace the method in the original class
        	cgen.replaceMethod(m, newMethod);
		}
		return;
	}

	public Object findInstructionValue(ConstantPoolGen cpgen, Instruction ins, HashMap localVars) {
		Object value = null;

		if (ins instanceof LDC) {
			value = ((LDC)ins).getValue(cpgen);
		} else if (ins instanceof LDC2_W) {
			value = ((LDC2_W)ins).getValue(cpgen);
		} else if (ins instanceof ConstantPushInstruction) {
			value = ((ConstantPushInstruction)ins).getValue();
		} else if (ins instanceof LoadInstruction) {
			// find the value in the map
			int index = ((LoadInstruction)ins).getIndex();
			value = localVars.get(index);
		} else {
			System.out.println("Error");
			System.exit(1);
		}
		return value;
	}

	public boolean isNumericOperation(Instruction ins) {
		String insName = ins.getName();
		if (normalMultivariateOperationsList.contains(insName)) {
			return true;
		} 
		if (typeCastOperationList.contains(insName)) {
			return true;
		}
		if (negOperationList.contains(insName)) {
			return true;
		}
		if (multiValueControlFlowList.contains(insName)){
			return true;
		}
		if (singleValueControlFlowList.contains(insName)) {
			return true;
		}													//debug for comparsion
		return false;
	}

	public boolean isUnaryOperation(Instruction ins) {
		String insName = ins.getName();
		if (typeCastOperationList.contains(insName)) {
			return true;
		}
		if (negOperationList.contains(insName)) {
			return true;
		}
		return false;
	}

	public boolean isMultivariateOperation(Instruction ins) {
		String insName = ins.getName();
		if (normalMultivariateOperationsList.contains(insName)) {
			return true;
		}
																//debug for comparsion
		return false;
	}
	public boolean isTypeCastingOperation(Instruction ins) {
		String insName = ins.getName();
		if (typeCastOperationList.contains(insName)) {
			return true;
		}
		return false;
	}
	public boolean isNegativeOperation(Instruction ins) {
		String insName = ins.getName();
		if (negOperationList.contains(insName)) {
			return true;
		}
		return false;
	}
	public boolean isMultiControlFlowOperation(Instruction ins) {
		String insName = ins.getName();
		if (multiValueControlFlowList.contains(insName)) {
			return true;
		}
		return false;
	}
	public boolean isSingleControlFlowOperation(Instruction ins) {
		String insName = ins.getName();
		if (singleValueControlFlowList.contains(insName)) {
			return true;
		}
		return false;
	}


	public InstructionHandle findOptimizedTypeCastingInsHandle(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName, Object value) {
		if (insName == "i2d") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).doubleValue()));
		} else if (insName == "i2l") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).longValue()));
		} else if (insName == "i2f") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).floatValue()));
		} else if (insName == "d2i") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).intValue()));
		} else if (insName == "d2l") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).longValue()));
		} else if (insName == "d2f") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).floatValue()));
		} else if (insName == "f2i") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).intValue()));
		} else if (insName == "f2d") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).floatValue()));
		} else if (insName == "f2l") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).longValue()));
		} else if (insName == "l2i") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).intValue()));
		} else if (insName == "l2d") {
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).doubleValue()));
		} else{
			return insList.insert(insHandle, new PUSH(cpgen, ((Number)value).floatValue()));
		}
	}

	public InstructionHandle findOptimizedNegativeInsHandle(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName, Object value) {
		if (insName == "ineg") {
			return insList.insert(insHandle, new PUSH(cpgen, -(int)value));
		} else if (insName == "dneg") {
			return insList.insert(insHandle, new PUSH(cpgen, -(double)value));
		} else if (insName == "fneg") {
			return insList.insert(insHandle, new PUSH(cpgen, -(float)value));
		} else {
			return insList.insert(insHandle, new PUSH(cpgen, -(float)value));
		}
	}

	public InstructionHandle findOptimizedMultivariateInsHandle(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName, Object o1, Object o2) {
		if (insName == "iadd") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 + (int)o2));
		}
		if (insName == "ladd") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 + (long)o2));
		}
		if (insName == "dadd") {
			return insList.insert(insHandle, new PUSH(cpgen, (double)o1 + (double)o2));
		}
		if (insName == "fadd") {
			return insList.insert(insHandle, new PUSH(cpgen, (float)o1 + (float)o2));
		}
		if (insName == "isub") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 - (int)o2));
		}
		if (insName == "lsub") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 - (long)o2));
		}
		if (insName == "dsub") {
			return insList.insert(insHandle, new PUSH(cpgen, (double)o1 - (double)o2));
		}
		if (insName == "fsub") {
			return insList.insert(insHandle, new PUSH(cpgen, (float)o1 - (float)o2));
		}
		if (insName == "imul") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 * (int)o2));
		}
		if (insName == "lmul") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 * (long)o2));
		}
		if (insName == "dmul") {
			return insList.insert(insHandle, new PUSH(cpgen, (double)o1 * (double)o2));
		}
		if (insName == "fmul") {
			return insList.insert(insHandle, new PUSH(cpgen, (float)o1 * (float)o2));
		}
		if (insName == "idiv") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 / (int)o2));
		}
		if (insName == "ldiv") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 / (long)o2));
		}
		if (insName == "ddiv") {
			return insList.insert(insHandle, new PUSH(cpgen, (double)o1 / (double)o2));
		}
		if (insName == "fdiv") {
			return insList.insert(insHandle, new PUSH(cpgen, (float)o1 / (float)o2));
		}
		if (insName == "irem") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 % (int)o2));
		}
		if (insName == "lrem") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 % (long)o2));
		}
		if (insName == "drem") {
			return insList.insert(insHandle, new PUSH(cpgen, (double)o1 % (double)o2));
		}
		if (insName == "frem") {
			return insList.insert(insHandle, new PUSH(cpgen, (float)o1 % (float)o2));
		}
		if (insName == "ishl") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 << (int)o2));
		}
		if (insName == "lshl") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 << (long)o2));
		}
		if (insName == "ishr") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 >> (int)o2));
		}
		if (insName == "lshr") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 >> (long)o2));
		}
		if (insName == "iushr") {
			return insList.insert(insHandle, new PUSH(cpgen, (int)o1 >>> (int)o2));
		}
		if (insName == "lushr") {
			return insList.insert(insHandle, new PUSH(cpgen, (long)o1 >>> (long)o2));
		}
		if ((insName == "dcmpl") || (insName == "dcmpg")) {
			if ((double)o1 > (double)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, 1));
			} else if ((double)o1 < (double)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, -1));
			} else {
				return insList.insert(insHandle, new PUSH(cpgen, 0));
			}
		}
		if ((insName == "fcmpl") || (insName == "fcmpg")) {
			if ((float)o1 > (float)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, 1));
			} else if ((float)o1 < (float)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, -1));
			} else {
				return insList.insert(insHandle, new PUSH(cpgen, 0));
			}
		}
		if (insName == "lcmp") {
			if ((long)o1 > (long)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, 1));
			} else if ((long)o1 < (long)o2) {
				return insList.insert(insHandle, new PUSH(cpgen, -1));
			} else {
				return insList.insert(insHandle, new PUSH(cpgen, 0));
			}
		}
		return null;
	}

	public InstructionHandle findOptimizedMultiControlFlowHandle(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName, Object value1, Object value2) {
		Instruction ins = insHandle.getInstruction();
		InstructionHandle target = null;
		InstructionHandle current;

		if (insName == "if_icmpeq") {
			if ((int)value1 == (int)value2) {
				target = ((IF_ICMPEQ)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
			
		} else if (insName == "if_icmpge") {
			if ((int)value1 >= (int)value2) {
				target = ((IF_ICMPGE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} 
		} else if (insName == "if_icmpgt") {
			if ((int)value1 > (int)value2) {
				target = ((IF_ICMPGT)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "if_icmple") {
			if ((int)value1 < (int)value2) {
				target = ((IF_ICMPLE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "if_icmplt") {
			if ((int)value1 <= (int)value2) {
				target = ((IF_ICMPLE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else  {
			if ((int)value1 != (int)value2) {
				target = ((IF_ICMPLE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev().getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev().getPrev(), insHandle);
					
					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		}
		return target;
	}

	public InstructionHandle findOptimizedSingleControlFlowHandle(ConstantPoolGen cpgen, InstructionList insList, InstructionHandle insHandle, String insName, Object value) {
		Instruction ins = insHandle.getInstruction();
		InstructionHandle target = null;
		InstructionHandle current;

		if (insName == "ifeq") {
			if ((int)value == 0) {
				target = ((IFEQ)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
					System.out.println("D S!!!!!");
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "ifge") {
			if ((int)value  >= 0) {
				target = ((IFGE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "ifgt") {
			if ((int)value  > 0) {
				target = ((IFGT)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "ifle") {
			if ((int)value  < 0) {
				target = ((IFLE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else if (insName == "iflt") {
			if ((int)value  <= 0) {
				target = ((IFLT)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		} else {
			if ((int)value != 0) {
				target = ((IFNE)ins).getTarget();
				try {
					insList.delete(insHandle.getPrev(), target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			} else {
				try {
					current = insHandle;
					while (!(current.getInstruction() instanceof GOTO)) {
						current = current.getNext();
					}

					insList.delete(insHandle.getPrev(), insHandle);

					target=((GOTO)current.getInstruction()).getTarget();
					insList.delete(current, target.getPrev());
				} catch (TargetLostException e) {
					e.printStackTrace();
				}
			}
		}
		return target;
	}

	public int containsLoop(InstructionList insList) {
		int numOfLoops = 0;
		InstructionHandle[] insHandles = insList.getInstructionHandles();

		for (InstructionHandle insHandle : insHandles) {
			if (insHandle.getInstruction() instanceof BranchInstruction) {
				if (((BranchInstruction)(insHandle.getInstruction())).getTarget().getPosition() < insHandle.getPosition()) {
					numOfLoops++;
				}
			}
		}
		return numOfLoops;
	}

	public ArrayList<Integer> getLoopStartPositions(InstructionList insList) {
		ArrayList<Integer> a = new ArrayList<Integer>();
		InstructionHandle[] insHandles = insList.getInstructionHandles();
		InstructionHandle goToTarget = null;

		for (InstructionHandle insHandle : insHandles) {
			if (insHandle.getInstruction() instanceof BranchInstruction) {
				if (((BranchInstruction)(insHandle.getInstruction())).getTarget().getPosition() < insHandle.getPosition()) {
					goToTarget = ((BranchInstruction)(insHandle.getInstruction())).getTarget();
					while (!(goToTarget.getInstruction() instanceof BranchInstruction)) {
						goToTarget = goToTarget.getNext();
					}
					a.add(goToTarget.getPosition());
				}
			}
		}
		return a;
	}
	
	public ArrayList<Integer> getLoopEndPosition(InstructionList insList, ArrayList<Integer> a) {
		ArrayList<Integer> result = new ArrayList<Integer>();
		Iterator itr = a.iterator();
		InstructionHandle target = null;
		while (itr.hasNext()) {
			int next = (int)itr.next();
			Instruction ins = insList.findHandle(next).getInstruction();
			target = ((BranchInstruction)ins).getTarget();
			result.add(target.getPosition());
		}
		return result;
	}
	
	public boolean isLoopStartPosition(ArrayList<Integer> loopStartPositions, int currentPosition) {
		Iterator itrStart = loopStartPositions.iterator();
		while (itrStart.hasNext()) {
			int nextStart = (int)itrStart.next();
			if (currentPosition == nextStart) {
				return true;
			}
		}
		return false;
	}

	public int findLoopEndPosition(ArrayList<Integer> start, ArrayList<Integer> end, int currentPosition) {
		int result = -1;
		//find which loop
		int index = 0;
		Iterator itr = start.iterator();
		while (itr.hasNext()) {
			if (currentPosition == (int)itr.next()){
				result = (int)end.get(index);
			}
			index++;
		}
		return result;
	}

	
	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}