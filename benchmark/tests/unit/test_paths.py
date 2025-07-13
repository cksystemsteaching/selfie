import unittest
from unittest.mock import patch, MagicMock
from pathlib import Path
from lib.paths import OutputPath, BaseSourcePath, LoadSourcePath, SourcePath

import lib.exceptions as ex  # Replace with your actual module
import lib.config as cfg  # Replace with your config module


class TestOutputPath(unittest.TestCase):
    @patch.object(Path, "exists")
    @patch.object(Path, "is_dir")
    def test_validation(self, mock_is_dir, mock_exists):
        """Test parent directory validation"""
        mock_exists.return_value = True
        mock_is_dir.return_value = True

        # Test valid path
        path = OutputPath("/valid/path/file.txt")
        self.assertEqual(str(path), "/valid/path/file.txt")

        # Test parent doesn't exist
        mock_exists.return_value = False
        with self.assertRaises(ex.FileValidationError):
            OutputPath("/invalid/path/file.txt")

        # Test parent not a directory
        mock_exists.return_value = True
        mock_is_dir.return_value = False
        file = "/file/instead/of/dir/file.txt"
        with self.assertRaises(ex.FileValidationError) as cm:
            OutputPath(file)

        exception = cm.exception
        self.assertIn("not a directory", str(exception))
        self.assertEqual(exception.context["path"], file)

    def test_as_file_for(self):
        """Test file path generation"""
        with patch.object(Path, "exists", return_value=True), patch.object(
            Path, "is_dir", return_value=True
        ):

            # Directory case
            dir_path = OutputPath("/output/dir")
            file_path = dir_path.as_file_for("model", "txt")
            self.assertEqual(str(file_path), "/output/dir/model.txt")

            # File case (should return self)
            orig_path = OutputPath("/existing/file.txt")
            self.assertIs(orig_path.as_file_for("ignore", "txt"), orig_path)


class TestBaseSourcePath(unittest.TestCase):
    @patch.object(Path, "exists")
    def test_validation(self, mock_exists):
        """Test basic source validation"""
        mock_exists.return_value = True
        path = BaseSourcePath("/existing/file.txt")
        self.assertEqual(str(path), "/existing/file.txt")

        mock_exists.return_value = False
        with self.assertRaises(ex.FileValidationError):
            BaseSourcePath("/nonexistent/file.txt")


class TestLoadSourcePath(unittest.TestCase):
    @patch.object(Path, "exists", return_value=True)
    @patch.dict(cfg.config, {"allowed_formats": ["txt", "json"]}, clear=True)
    def test_format_validation(self, _):
        """Test format validation"""
        with patch.object(Path, "suffix", ".txt"):
            LoadSourcePath("/valid.txt")  # Should pass

        with patch.object(Path, "suffix", ".csv"):
            with self.assertRaises(ex.FileValidationError):
                LoadSourcePath("/invalid.csv")

        # Directory should bypass format check
        with patch.object(Path, "is_dir", return_value=True):
            LoadSourcePath("/any/directory/")


class TestSourcePath(unittest.TestCase):
    @patch.object(Path, "exists", return_value=True)
    @patch.dict(cfg.config, {"allowed_languages": [".py", ".c"]}, clear=True)
    def test_language_validation(self, _):
        """Test language extension validation"""
        with patch.object(Path, "suffix", ".py"):
            SourcePath("/valid.py")  # Should pass

        with patch.object(Path, "suffix", ".java"):
            with self.assertRaises(ex.FileValidationError):
                SourcePath("/invalid.java")

        # Directory should bypass language check
        with patch.object(Path, "is_dir", return_value=True):
            SourcePath("/any/directory/")


class TestPathDelegation(unittest.TestCase):
    def test_path_delegation(self):
        """Test Path-like behavior"""
        with patch.object(Path, "exists", return_value=True), patch.object(
            Path, "is_dir", return_value=True
        ):

            path = OutputPath("/test/path")
            # Test attribute delegation
            with patch.object(Path, "stem", "mocked_stem"):
                self.assertEqual(path.stem, "mocked_stem")

            # Test fspath protocol
            self.assertEqual(str(path), "/test/path")
