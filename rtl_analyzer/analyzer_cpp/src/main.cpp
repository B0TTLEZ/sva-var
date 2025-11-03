#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <filesystem>
#include <stdexcept> // 用于 std::stoi 的异常处理

#include "slang/ast/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "DataModel.h"
#include "DependencyVisitor.h"
#include "ProgramSlicer.h"
#include "json.hpp"
#include "slang/diagnostics/DiagnosticEngine.h"  
#include "slang/diagnostics/TextDiagnosticClient.h"  

struct TestCase {
        std::string name;
        std::string topModule;
        std::vector<std::string> sourceFiles;
        std::vector<std::string> headerFiles;
        std::string outputPath;
    };

    std::vector<TestCase> testSuite = {  
    {  
        "Basic Dataflow",  
        "test_basic_dataflow",  
        {"/data/fhj/sva-var/test_suite/test_basic_dataflow.sv"},  
        {},  
        "../../results/test_basic_dataflow.json"  
    },  
    {  
        "Case Statement",  
        "test_case_statement",  
        {"/data/fhj/sva-var/test_suite/test_case_statement.sv"},  
        {},  
        "../../results/test_case_statement.json"  
    },  
    {  
        "Nested Conditions",  
        "test_nested_conditions",  
        {"/data/fhj/sva-var/test_suite/test_nested_conditions.sv"},  
        {},  
        "../../results/test_nested_conditions.json"  
    },  
    {  
        "Module Hierarchy",  
        "test_module_hierarchy",  
        {"/data/fhj/sva-var/test_suite/test_module_hierarchy.sv"},  
        {},  
        "../../results/test_module_hierarchy.json"  
    },  
    {  
        "Struct Union",  
        "test_struct_union",  
        {"/data/fhj/sva-var/test_suite/test_struct_union.sv"},  
        {},  
        "../../results/test_struct_union.json"  
    },  
    {  
        "Parameters Enums",  
        "test_parameters_enums",  
        {"/data/fhj/sva-var/test_suite/test_parameters_enums.sv"},  
        {},  
        "../../results/test_parameters_enums.json"  
    },  
    {  
        "Increment Operations",  
        "test_increment_operations",  
        {"/data/fhj/sva-var/test_suite/test_increment_operations.sv"},  
        {},  
        "../../results/test_increment_operations.json"  
    } 
    ,  
    {  
        "Verilog Counter",  
        "test_verilog_counter",  
        {"/data/fhj/sva-var/test_suite/test_verilog_counter.v"},  
        {},  
        "../../results/test_verilog_counter.json"  
    },  
    {  
        "Verilog FSM",  
        "test_verilog_fsm",  
        {"/data/fhj/sva-var/test_suite/test_verilog_fsm.v"},  
        {},  
        "../../results/test_verilog_fsm.json"  
    }
};
// 注意：为了运行此代码，您需要取消注释 testSuite 中您希望运行的测试用例。
// 目前，只有 Ibex Core 测试用例是启用状态。
// std::vector<TestCase> testSuite = {
//         {
//             "i2c",
//             "i2c_master_top",
//             {   
//                 "/data/fhj/sva-var/datasets/AssertEval/i2c/rtl/i2c_master_defines.v",
//                 "/data/fhj/sva-var/datasets/AssertEval/i2c/rtl/i2c_master_top.v",
//                 "/data/fhj/sva-var/datasets/AssertEval/i2c/rtl/i2c_master_bit_ctrl.v",
//                 "/data/fhj/sva-var/datasets/AssertEval/i2c/rtl/i2c_master_byte_ctrl.v"
//             },
//             {
//                 "/data/fhj/sva-var/datasets/AssertEval/i2c/rtl/i2c_master_defines.v"
//             },
//             "../../results/i2c.json"
//         },
//         {
//             "apb",
//             "i2c",
//             {
//                 "/data/fhj/sva-var/datasets/AssertEval/apb/rtl/apb.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/apb/rtl/fifo.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/apb/rtl/i2c.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/apb/rtl/module_i2c.sv"
//             },
//             {},
//             "../../results/apb.json"
//         },
//         {
//             "uart",
//             "uart2bus_top",
//             {
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/uart_rx.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/uart_tx.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/uart_parser.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/baud_gen.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/uart_top.sv",
//                 "/data/fhj/sva-var/datasets/AssertEval/uart/rtl/uart2bus_top.sv"
//             },
//             {
                
//             },
//             "../../results/uart.json"
//         },
//         // --- 现有测试用例 (已注释) ---
//         // {
//         //     "Basic Dataflow",
//         //     "test_basic",
//         //     {"../test_suite/1_basic_dataflow/test_basic.sv"},
//         //     {},
//         //     "../../results/1_basic_dataflow.json"
//         // },
        
//         // --- 新增 Ibex 测试用例 ---
//         // {
//         //     "Ibex Compressed Decoder",
//         //     "ibex_compressed_decoder",
//         //     {"/data/fhj/sva-var/ibex/rtl/ibex_compressed_decoder.sv"},
//         //     {
//         //         "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_dummy_macros.svh",
//         //         "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_yosys_macros.svh",
//         //         // ... 其他头文件
//         //     },
//         //     "../../results/ibex_compressed_decoder.json"
//         // },
//         {
//             "Ibex Core",
//             "ibex_core", // 假设顶层模块名是 ibex_core
//             {
//                 "/data/fhj/sva-var/ibex/rtl/ibex_alu.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_compressed_decoder.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_controller.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_counter.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_cs_registers.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_decoder.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_ex_block.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_id_stage.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_if_stage.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_load_store_unit.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_multdiv_slow.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_multdiv_fast.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_prefetch_buffer.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_fetch_fifo.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_register_file_ff.sv",
//                 "/data/fhj/sva-var/ibex/rtl/ibex_csr.sv", 
//                 "/data/fhj/sva-var/ibex/rtl/ibex_wb_stage.sv",  
//                 "/data/fhj/sva-var/ibex/rtl/ibex_core.sv"
//             },
//             {   
//                 "/data/fhj/sva-var/ibex/rtl/ibex_pkg.sv",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_dummy_macros.svh",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_yosys_macros.svh",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_standard_macros.svh",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert_sec_cm.svh",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_flop_macros.sv",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv",
//                 "/data/fhj/sva-var/ibex/vendor/lowrisc_ip/dv/sv/dv_utils/dv_fcov_macros.svh"
                
//             },
//             "../../results/ibex_core.json"
//         }
//     };


using json = nlohmann::json;

// JSON 序列化辅助函数 (保持不变)
void to_json(json& j, const ConditionExpression& expr) {
    j = json{
        {"expression", expr.expression},
        {"involvedSignals", expr.involvedSignals},
        {"involvedParameters", expr.involvedParameters}
    };
}

void to_json(json& j, const ConditionClause& c) {
    j = json{
        {"expr", c.expr},
        {"polarity", c.polarity}
    };
}

void to_json(json& j, const AssignmentInfo& a) {
    j = json{
        {"path", a.path},
        {"drivingSignals", a.drivingSignals},
        {"file", a.file},
        {"line", a.line},
        {"type", a.type},
        {"logicType", a.logicType},
        {"conditionDepth", a.conditionDepth}
    };
}

void to_json(json& j, const VariableInfo& v) {
    j = json{
        {"fullName", v.fullName},
        {"type", v.type},
        {"file", v.fileName},
        {"line", v.line},
        {"direction", v.direction},
        {"bitWidth", v.bitWidth},
        {"assignments", v.assignments},
        {"fanOut", v.fanOut},
        {"assignmentCount", v.assignmentCount},
        {"drivesOutput", v.drivesOutput},
        {"isControlVariable", v.isControlVariable}
    };
}

// 核心分析函数 (保持不变)
bool runAnalysis(const std::string& topModule,   
                 const std::vector<std::string>& sourceFiles,  
                 const std::vector<std::string>& headerFiles,  
                 const std::string& outputPath,
                 const SlicingCriterion* criterion = nullptr) {  
      
    std::cout << "--- Analyzing Test Case: " << topModule << " ---" << std::endl;  
    std::cout << "Source files: " << sourceFiles.size() << std::endl;  
    std::cout << "Header files: " << headerFiles.size() << std::endl;  
  
    std::filesystem::path outPath(outputPath);  
    if (outPath.has_parent_path()) {  
        std::filesystem::create_directories(outPath.parent_path());  
    }  

    std::set<std::string> uniqueIncludePaths;
    for (const auto& headerFile : headerFiles) {
        std::filesystem::path headerPath(headerFile);
        if (headerPath.has_parent_path()) {
            uniqueIncludePaths.insert(headerPath.parent_path().string());
        }
    }
    std::vector<std::filesystem::path> finalIncludePaths;
    for (const auto& pathString : uniqueIncludePaths) {
        finalIncludePaths.push_back(std::filesystem::path(pathString));
    }

    // 创建 SourceManager  
    slang::SourceManager sourceManager;  
      
    // 配置预处理器选项,添加 include 路径  
    slang::parsing::PreprocessorOptions ppOptions; 
      
    slang::Bag options;  
    options.set(ppOptions);  
      
    // 重要:使用带 options 的 Compilation 构造函数  
    slang::ast::Compilation compilation(options);  
      
    // 首先添加头文件 - 传递 sourceManager 和 options  
    for (const auto& headerFile : headerFiles) {  
        if (!std::filesystem::exists(headerFile)) {  
            std::cerr << "[WARNING] Header file not found: " << headerFile << std::endl;  
            continue;  
        }  
        // 关键修改:传递 sourceManager 和 options  
        auto tree_expected = slang::syntax::SyntaxTree::fromFile(headerFile, sourceManager, options);  
        if (!tree_expected) {  
            std::cerr << "[WARNING] Failed to parse header file: " << headerFile << std::endl;  
            continue;  
        }  
        compilation.addSyntaxTree(*tree_expected);  
        std::cout << "[INFO] Added header file: " << headerFile << std::endl;  
    }  
      
    // 然后添加源文件 - 同样传递 sourceManager 和 options  
    for (const auto& sourceFile : sourceFiles) {  
        if (!std::filesystem::exists(sourceFile)) {  
            std::cerr << "[ERROR] Source file not found: " << sourceFile << std::endl;  
            return false;  
        }  
        // 关键修改:传递 sourceManager 和 options  
        auto tree_expected = slang::syntax::SyntaxTree::fromFile(sourceFile, sourceManager, options);  
        if (!tree_expected) {  
            std::cerr << "[ERROR] Failed to parse source file: " << sourceFile << std::endl;  
            return false;  
        }  
        compilation.addSyntaxTree(*tree_expected);  
        std::cout << "[INFO] Added source file: " << sourceFile << std::endl;  
    }  
      
    auto& root = compilation.getRoot();  
      
    // // 输出顶层模块  
    // auto topInstances = root.topInstances;  
    // if (!topInstances.empty()) {  
    //     std::cout << "Top level design units:\n";  
    //     for (auto inst : topInstances)  
    //         std::cout << "    " << inst->name << "\n";  
    //     std::cout << "\n";  
    // }  
      
    // 创建诊断引擎和客户端  
    slang::DiagnosticEngine diagEngine(sourceManager);  
    auto textClient = std::make_shared<slang::TextDiagnosticClient>();  
    diagEngine.addClient(textClient);  
      
    // 发出所有诊断  
    for (auto& diag : compilation.getAllDiagnostics())  
        diagEngine.issue(diag);  
      
    // 输出诊断结果  
    std::cout << textClient->getString();  
      
    // 检查是否有错误  
    int numErrors = diagEngine.getNumErrors();  
    if (numErrors > 0) {  
        std::cerr << "[FAILED] Build failed: " << numErrors << " errors\n";  
        return false;  
    }  
      
    std::cout << "[SUCCESS] Build succeeded\n";  
      
    // 查找顶层模块  
    const slang::ast::InstanceSymbol* top = nullptr;  
    for (auto inst : root.topInstances) {  
        if (inst->name == topModule) {  
            top = inst;  
            break;  
        }  
    }  
      
    if (!top) {  
        std::cerr << "[ERROR] Top module '" << topModule << "' not found." << std::endl;  
        return false;  
    }  
      
    DependencyVisitor visitor;    
    top->visit(visitor);    
    visitor.postProcess();  
      
    // 创建 ProgramSlicer 对象  
    ProgramSlicer slicer(visitor.getResults());  
      
    // 创建默认配置    
    SliceConfig config;    
    config.granularity = SliceGranularity::ProceduralBlock;    
    config.filterOptions = SliceFilterOptions::RemoveUnrelatedAssignments;    
    config.contextLines = 0;    
        
    json unifiedOutput;    
    unifiedOutput["topModule"] = topModule;    
    unifiedOutput["analysisResults"] = visitor.getResults();    
    // 准备txt文件输出  
    std::stringstream txtOutput;  
    txtOutput << "========================================\n";  
    txtOutput << "Program Slices for Module: " << topModule << "\n";  
    txtOutput << "========================================\n\n";    

    // 为每个变量生成前向和后向切片    
    for (const auto& [varName, varInfo] : visitor.getResults()) {    
        SlicingCriterion backwardCriterion;    
        backwardCriterion.variableName = varName;    
          
        SliceResult backwardResult = slicer.backwardSlice(backwardCriterion, config);    
        SliceResult forwardResult = slicer.forwardSlice(backwardCriterion, config);    
          
        std::string backwardCode = slicer.generateMergedCodeForVariable(    
            backwardResult, varName, sourceManager);    
        std::string forwardCode = slicer.generateMergedCodeForVariable(    
            forwardResult, varName, sourceManager);    
        // 添加到txt输出  
        txtOutput << "========================================\n";  
        txtOutput << "Variable: " << varName << "\n";  
        txtOutput << "========================================\n\n";  
          
        txtOutput << "--- Backward Slice ---\n";  
        txtOutput << backwardCode << "\n\n";  
          
        txtOutput << "--- Forward Slice ---\n";  
        txtOutput << forwardCode << "\n\n";  
          
        txtOutput << "----------------------------------------\n\n";   
        unifiedOutput["slices"][varName]["backward"]["mergedCode"] = backwardCode;    
        unifiedOutput["slices"][varName]["backward"]["metadata"] = {    
            {"relevantVariables", backwardResult.relevantVariables},    
            {"controlVariables", backwardResult.controlVariables}    
        };    
          
        unifiedOutput["slices"][varName]["forward"]["mergedCode"] = forwardCode;    
        unifiedOutput["slices"][varName]["forward"]["metadata"] = {    
            {"relevantVariables", forwardResult.relevantVariables},    
            {"controlVariables", forwardResult.controlVariables}    
        };    
    }     
     
    // 输出到文件    
    std::ofstream outFile(outputPath);    
    if (outFile.is_open()) {    
        outFile << unifiedOutput.dump(2);    
        outFile.close();    
        std::cout << "[SUCCESS] Results written to: " << outputPath << std::endl;    
    }    
         // 输出TXT文件  
    std::string txtPath = outputPath + ".slices.txt";  
    std::ofstream txtFile(txtPath);  
    if (txtFile.is_open()) {  
        txtFile << txtOutput.str();  
        txtFile.close();  
        std::cout << "[SUCCESS] Text slices written to: " << txtPath << std::endl;  
        return true;  
    } else {  
        std::cerr << "[ERROR] Could not open txt file for writing: " << txtPath << std::endl;  
        return false;  
    }     
    return false;   
}

/**
 * 主函数，作为测试驱动器
 * 允许用户选择运行单个测试或所有测试。
 */
int main(int argc, char** argv) {
    if (testSuite.empty()) {
        std::cout << "No test cases are currently defined or uncommented in testSuite." << std::endl;
        return 0;
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Available Test Cases:" << std::endl;
    for (size_t i = 0; i < testSuite.size(); ++i) {
        std::cout << "[" << i + 1 << "] " << testSuite[i].name << std::endl;
    }
    std::cout << "[0] Run ALL Tests" << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "Enter selection (1-" << testSuite.size() << ", or 0 for all): ";

    std::string input;
    std::cin >> input;

    std::vector<TestCase> selectedTests;
    int index = -1;

    try {
        index = std::stoi(input);
    } catch (const std::invalid_argument& e) {
        std::cerr << "Invalid input. Please enter a number (0-" << testSuite.size() << ")." << std::endl;
        return 1;
    } catch (const std::out_of_range& e) {
        std::cerr << "Invalid selection: Index out of range." << std::endl;
        return 1;
    }


    if (index == 0) {
        selectedTests = testSuite; // 运行所有测试
        std::cout << "Executing ALL " << testSuite.size() << " test cases." << std::endl;
    } else if (index >= 1 && index <= (int)testSuite.size()) {
        selectedTests.push_back(testSuite[index - 1]); // 索引是 1-based
        std::cout << "Executing selected test: " << testSuite[index - 1].name << std::endl;
    } else {
        std::cerr << "Invalid selection: Index out of range (Must be 0-" << testSuite.size() << ")." << std::endl;
        return 1;
    }

    std::cout << "----------------------------------------" << std::endl;


    // 执行选定的测试
    int successCount = 0;
    for (const auto& testCase : selectedTests) {
        std::cout << "\n========================================" << std::endl;
        std::cout << "Running: " << testCase.name << std::endl;
        std::cout << "========================================" << std::endl;
        
        if (runAnalysis(testCase.topModule, testCase.sourceFiles, testCase.headerFiles, testCase.outputPath)) {
            successCount++;
            std::cout << "✓ PASSED: " << testCase.name << std::endl;
        } else {
            std::cerr << "✗ FAILED: " << testCase.name << std::endl;
        }
    }

    std::cout << "\n========================================" << std::endl;
    std::cout << "Test Suite Finished." << std::endl;
    std::cout << "Passed: " << successCount << " / " << selectedTests.size() << std::endl;
    std::cout << "========================================" << std::endl;

    return (successCount == selectedTests.size()) ? 0 : 1;
}