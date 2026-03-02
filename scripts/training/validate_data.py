#!/usr/bin/env python3
"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                      // hydrogen // training // data // validate
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Validate training data quality for Hydrogen Engram model.

Checks:
1. JSON format validity
2. Required fields present
3. Message structure (system, user, assistant)
4. Token length distribution
5. Sample examples for manual review

────────────────────────────────────────────────────────────────────────────────
"""

import json
import sys
from pathlib import Path
from collections import Counter
import statistics

def count_tokens(text: str) -> int:
    """Rough token count (words * 1.3)."""
    return int(len(text.split()) * 1.3)

def validate_example(example: dict, line_num: int) -> list[str]:
    """Validate a single training example. Returns list of issues."""
    issues = []
    
    # Check for messages field
    if "messages" not in example:
        issues.append(f"Line {line_num}: Missing 'messages' field")
        return issues
    
    messages = example["messages"]
    
    # Check message count
    if len(messages) < 2:
        issues.append(f"Line {line_num}: Too few messages ({len(messages)})")
    
    # Check roles
    roles = [m.get("role") for m in messages]
    
    if "user" not in roles:
        issues.append(f"Line {line_num}: Missing user message")
    
    if "assistant" not in roles:
        issues.append(f"Line {line_num}: Missing assistant message")
    
    # Check content not empty
    for i, msg in enumerate(messages):
        if not msg.get("content", "").strip():
            issues.append(f"Line {line_num}: Empty content in message {i}")
    
    return issues

def validate_file(filepath: Path) -> dict:
    """Validate a JSONL training file."""
    results = {
        "filepath": str(filepath),
        "total_lines": 0,
        "valid_examples": 0,
        "invalid_examples": 0,
        "issues": [],
        "token_counts": [],
        "role_counts": Counter(),
        "examples_by_length": {"short": 0, "medium": 0, "long": 0}
    }
    
    with open(filepath, 'r') as f:
        for line_num, line in enumerate(f, 1):
            results["total_lines"] += 1
            
            if not line.strip():
                continue
            
            try:
                example = json.loads(line)
            except json.JSONDecodeError as e:
                results["issues"].append(f"Line {line_num}: JSON parse error - {e}")
                results["invalid_examples"] += 1
                continue
            
            # Validate structure
            issues = validate_example(example, line_num)
            if issues:
                results["issues"].extend(issues)
                results["invalid_examples"] += 1
            else:
                results["valid_examples"] += 1
            
            # Count tokens
            if "messages" in example:
                total_tokens = 0
                for msg in example["messages"]:
                    content = msg.get("content", "")
                    tokens = count_tokens(content)
                    total_tokens += tokens
                    results["role_counts"][msg.get("role", "unknown")] += 1
                
                results["token_counts"].append(total_tokens)
                
                if total_tokens < 200:
                    results["examples_by_length"]["short"] += 1
                elif total_tokens < 500:
                    results["examples_by_length"]["medium"] += 1
                else:
                    results["examples_by_length"]["long"] += 1
    
    return results

def print_results(results: dict):
    """Print validation results."""
    print(f"\n{'='*60}")
    print(f"Validation: {results['filepath']}")
    print(f"{'='*60}")
    
    print(f"\nSummary:")
    print(f"  Total lines: {results['total_lines']}")
    print(f"  Valid examples: {results['valid_examples']}")
    print(f"  Invalid examples: {results['invalid_examples']}")
    
    if results['token_counts']:
        print(f"\nToken Statistics:")
        print(f"  Min tokens: {min(results['token_counts'])}")
        print(f"  Max tokens: {max(results['token_counts'])}")
        print(f"  Mean tokens: {statistics.mean(results['token_counts']):.1f}")
        print(f"  Median tokens: {statistics.median(results['token_counts']):.1f}")
    
    print(f"\nLength Distribution:")
    print(f"  Short (<200 tokens): {results['examples_by_length']['short']}")
    print(f"  Medium (200-500): {results['examples_by_length']['medium']}")
    print(f"  Long (>500): {results['examples_by_length']['long']}")
    
    print(f"\nRole Counts:")
    for role, count in sorted(results['role_counts'].items()):
        print(f"  {role}: {count}")
    
    if results['issues']:
        print(f"\nIssues ({len(results['issues'])} found):")
        for issue in results['issues'][:10]:
            print(f"  - {issue}")
        if len(results['issues']) > 10:
            print(f"  ... and {len(results['issues']) - 10} more")

def sample_examples(filepath: Path, n: int = 3):
    """Print sample examples for manual review."""
    print(f"\n{'='*60}")
    print(f"Sample Examples from {filepath.name}")
    print(f"{'='*60}")
    
    import random
    
    examples = []
    with open(filepath, 'r') as f:
        for line in f:
            if line.strip():
                examples.append(json.loads(line))
    
    samples = random.sample(examples, min(n, len(examples)))
    
    for i, ex in enumerate(samples, 1):
        print(f"\n--- Example {i} ---")
        for msg in ex.get("messages", []):
            role = msg.get("role", "?")
            content = msg.get("content", "")[:200]
            if len(msg.get("content", "")) > 200:
                content += "..."
            print(f"[{role}]: {content}")

def main():
    data_dir = Path("training/data")
    
    if not data_dir.exists():
        print(f"Error: {data_dir} not found")
        sys.exit(1)
    
    jsonl_files = list(data_dir.glob("*.jsonl"))
    
    if not jsonl_files:
        print(f"Error: No JSONL files found in {data_dir}")
        sys.exit(1)
    
    print(f"Found {len(jsonl_files)} training files")
    
    all_valid = True
    
    for filepath in sorted(jsonl_files):
        results = validate_file(filepath)
        print_results(results)
        
        if results['invalid_examples'] > 0:
            all_valid = False
    
    # Sample from combined dataset
    combined = data_dir / "hydrogen_schema_combined.jsonl"
    if combined.exists():
        sample_examples(combined)
    
    print(f"\n{'='*60}")
    if all_valid:
        print("All training data is valid!")
    else:
        print("Some issues found - review above")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()
